/*
 * https://pkware.cachefly.net/webdocs/casestudies/APPNOTE.TXT
 * https://source.android.com/docs/security/features/apksigning/
 * https://android.googlesource.com/platform/frameworks/base/+/refs/heads/main/core/java/android/util/apk
 */
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/stat.h>
#include <openssl/x509.h>
#include <openssl/evp.h>
#include <openssl/rsa.h>

#include "verifyapk.h"

#define GET16(p) (uint16_t)(((uint8_t*)(p))[0]|(((uint8_t*)(p))[1]<<8))
#define GET32(p) (uint32_t)(((uint8_t*)(p))[0]|(((uint8_t*)(p))[1]<<8)|(((uint8_t*)(p))[2]<<16)|(((uint8_t*)(p))[3]<<24))
#define GET64(p) (uint64_t)((uint32_t)(((uint8_t*)(p))[0]|(((uint8_t*)(p))[1]<<8)|(((uint8_t*)(p))[2]<<16)|(((uint8_t*)(p))[3]<<24))|((uint64_t)(((uint8_t*)(p))[4]|(((uint8_t*)(p))[5]<<8)|(((uint8_t*)(p))[6]<<16)|(((uint8_t*)(p))[7]<<24)) << 32))
#define PUT32(p,v) do{(p)[0]=(v);(p)[1]=(v)>>8;(p)[2]=(v)>>16;(p)[3]=(v)>>24;}while(0)

typedef struct Filectx Filectx;
struct Filectx {
	uint8_t eocd[22];
	uint32_t cdoff, cdsize, sblkoff, sblksize, filesize;
	int fd;
};

static const char *
verifydigest(Filectx *file, EVP_MD *mdalg, uint8_t *digp, uint32_t dign)
{
#define CHUNKSZ(x) (((x)+1048575)/1048576)
	const char *errstr;
	EVP_MD_CTX *chunkctx, *finalctx;
	unsigned int hn;
	uint32_t n, m, l;
	uint8_t h[EVP_MAX_MD_SIZE], buf[32768];

	errstr = "cant allocate md contexts";
	finalctx = NULL;
	chunkctx = EVP_MD_CTX_new();
	if(chunkctx == NULL)
		goto err;
	finalctx = EVP_MD_CTX_new();
	if(finalctx == NULL)
		goto err;

	errstr = "cant initialize md context";
	if(EVP_DigestInit_ex(finalctx, mdalg, NULL) <= 0)
		goto err;
	buf[0] = 0x5a;
	PUT32(buf+1, CHUNKSZ(file->sblkoff)+CHUNKSZ(file->cdsize)+1);
	if(EVP_DigestUpdate(finalctx, buf, 5) <= 0)
		goto err;

	if(lseek(file->fd, 0, SEEK_SET) == -1)
		goto err;
	errstr = "cant hash chunk";
	n = file->sblkoff;
	while(n > 0){
		if(EVP_DigestInit_ex(chunkctx, mdalg, NULL) <= 0)
			goto err;
		m = n < 1048576 ? n : 1048576;
		n -= m;
		buf[0] = 0xa5;
		PUT32(buf+1, m);
		if(EVP_DigestUpdate(chunkctx, buf, 5) <= 0)
			goto err;
		while(m > 0){
			l = m < sizeof(buf) ? m : sizeof(buf);
			if(read(file->fd, buf, l) != l)
				goto ferr;
			if(EVP_DigestUpdate(chunkctx, buf, l) <= 0)
				goto err;
			m -= l;
		}
		if(EVP_DigestFinal_ex(chunkctx, h, &hn) <= 0)
			goto err;
		if(EVP_DigestUpdate(finalctx, h, hn) <= 0)
			goto err;
		if(EVP_MD_CTX_reset(chunkctx) <= 0)
			goto err;
	}

	/* life is too short to worry about code duplication */
	if(lseek(file->fd, file->cdoff, SEEK_SET) == -1)
		goto err;
	n = file->cdsize;
	while(n > 0){
		if(EVP_DigestInit_ex(chunkctx, mdalg, NULL) <= 0)
			goto err;
		m = n < 1048576 ? n : 1048576;
		n -= m;
		buf[0] = 0xa5;
		PUT32(buf+1, m);
		if(EVP_DigestUpdate(chunkctx, buf, 5) <= 0)
			goto err;
		while(m > 0){
			l = m < sizeof(buf) ? m : sizeof(buf);
			if(read(file->fd, buf, l) < 0)
				goto ferr;
			if(EVP_DigestUpdate(chunkctx, buf, l) <= 0)
				goto err;
			m -= l;
		}
		if(EVP_DigestFinal_ex(chunkctx, h, &hn) <= 0)
			goto err;
		if(EVP_DigestUpdate(finalctx, h, hn) <= 0)
			goto err;
		if(EVP_MD_CTX_reset(chunkctx) <= 0)
			goto err;
	}

	buf[0] = 0xa5;
	PUT32(buf+1, sizeof(file->eocd));
	if(EVP_DigestInit_ex(chunkctx, mdalg, NULL) <= 0)
		goto err;
	if(EVP_DigestUpdate(chunkctx, buf, 5) <= 0)
		goto err;
	if(EVP_DigestUpdate(chunkctx, file->eocd, sizeof(file->eocd)) <= 0)
		goto err;
	if(EVP_DigestFinal_ex(chunkctx, h, &hn) <= 0)
		goto err;
	if(EVP_DigestUpdate(finalctx, h, hn) <= 0)
		goto err;
	if(EVP_DigestFinal_ex(finalctx, h, &hn) <= 0)
		goto err;

	errstr = "digest mismatch";
	if(hn != dign || memcmp(digp, h, hn) != 0)
		goto err;
	errstr = NULL;
	goto err;	 
ferr:
	errstr = strerror(errno);
err:
	EVP_MD_CTX_free(chunkctx);
	EVP_MD_CTX_free(finalctx);
	return errstr;
#undef CHUNKSZ
}


static const char *
parsesigner(Filectx *file, X509 *trusted, uint8_t *p, uint8_t *e, int *found)
{
	const char *errstr;
	X509 *cert;
	EVP_PKEY_CTX *evpctx;
	EVP_PKEY *pk, *certpk;
	EVP_MD *mdalg;
	const uint8_t *rp;
	unsigned int hn;
	uint32_t signedn, signaturen, dign, n;
	uint8_t *signedp, *signaturep, *digp, h[EVP_MAX_MD_SIZE];

	if(p+4 > e)
		return "broken signer";
	signedn = GET32(p), p += 4;
	if(p+signedn > e)
		return "signed data too big";
	signedp = p, p += signedn;
	if(p+4 > e)
		return "broken signer";
	n = GET32(p), p += 4;
	if(p+n > e)
		return "signatures too big";
	signaturep = NULL;
	while(n > 0 && signaturep == NULL){
		errstr = "signature broken";
		if(n < 4)
			return errstr;
		signaturen = GET32(p), p += 4, n -= 4;
		if(signaturen < 8 || signaturen > n)
			return errstr;
		if(GET32(p+4) != signaturen-8)
			return errstr;
		if(GET32(p) == 0x0103){ /* RSASSA-PKCS1-v1_5 SHA256 */
			signaturep = p+8;
			signaturen -= 8;
			p += 8, n -= 8;
		}
		p += signaturen;
		n -= signaturen;
	}
	if(signaturep == NULL)
		return "no signature found";

	errstr = "broken public key";
	if(p+4 > e)
		return errstr;
	n = GET32(p), p += 4;
	if(p+n != e)
		return errstr;

	errstr = "cant load public key";
	cert = NULL;
	certpk = NULL;
	evpctx = NULL;
	mdalg = NULL;
	rp = p;
	pk = d2i_PUBKEY(NULL, &rp, n);
	if(pk == NULL)
		goto err;
	evpctx = EVP_PKEY_CTX_new(pk, NULL);
	if(evpctx == NULL)
		goto err;
	if(EVP_PKEY_verify_init(evpctx) <= 0)
		goto err;
	if(EVP_PKEY_CTX_set_rsa_padding(evpctx, RSA_PKCS1_PADDING) <= 0)
		goto err;
	mdalg = EVP_MD_fetch(NULL, "SHA256", NULL);
	if(mdalg == NULL)
		goto err;
	if(EVP_PKEY_CTX_set_signature_md(evpctx, mdalg) <= 0)
		goto err;
	errstr = "signed data cant be verified";
	/* the first step of encoding, H = Hash(M), is expected to be done by the caller */
	if(EVP_Digest(signedp, signedn, h, &hn, mdalg, NULL) <= 0)
		goto err;
	if(EVP_PKEY_verify(evpctx, signaturep, signaturen, h, hn) <= 0)
		goto err;
	EVP_PKEY_CTX_free(evpctx);
	evpctx = NULL;

	errstr = "cant parse signed data";
	p = signedp;
	e = signedp+signedn;
	if(p+4 > e)
		goto err;
	n = GET32(p), p += 4;
	if(p+n > e)
		goto err;
	digp = NULL;
	while(n > 0 && digp == NULL){
		if(n < 4)
			goto err;
		dign = GET32(p), p += 4, n -= 4;
		if(dign < 8 || dign > n)
			goto err;
		if(GET32(p+4) != dign-8)
			goto err;
		if(GET32(p) == 0x0103){
			digp = p+8;
			dign -= 8;
			p += n;
			break;
		}
		p += dign;
		n -= dign;
	}
	if(digp == NULL){
		errstr = "cant find digest";
		goto err;
	}
	errstr = verifydigest(file, mdalg, digp, dign);
	if(errstr != NULL)
		goto err;
	EVP_MD_free(mdalg);
	mdalg = NULL;

	/* TODO: maybe return all certs to the user? */
	errstr = "broken cert";
	if(p+4 > e)
		goto err;
	n = GET32(p), p += 4;
	if(p+n > e)
		goto err;
	if(GET32(p)+4 > n)
		goto err;
	rp = p+4;
	cert = d2i_X509(NULL, &rp, GET32(p));
	if(cert == NULL)
		goto err;
	certpk = X509_get_pubkey(cert);
	if(certpk == NULL)
		goto err;
	p += n;
	errstr = "broken extensionsa";
	if(p+4+GET32(p) > e)
		goto err;

	errstr = "cert-public key mismatch";
	if(EVP_PKEY_eq(certpk, pk) != 1)
		goto err;
	EVP_PKEY_free(certpk);
	EVP_PKEY_free(pk);
	certpk = pk = NULL;
	if(X509_cmp(cert, trusted) == 0){
		if(*found){
			errstr = "more than one matching signers";
			goto err;
		}
		*found = 1;
	}

	errstr = NULL;
err:
	EVP_PKEY_CTX_free(evpctx);
	EVP_MD_free(mdalg);
	EVP_PKEY_free(pk);
	EVP_PKEY_free(certpk);
	X509_free(cert);
	return errstr;
}

static const char *
parsesignblk(Filectx *file, X509 *trusted, uint8_t *buf)
{
	const char *errstr;
	uint32_t id, n;
	uint8_t *p, *e;
	int found;

	p = buf;
	e = buf+file->sblksize-24;
	while(p < e){
		if(p+12 > e)
			return "broken signature block";
		n = GET64(p), p += 8;
		id = GET32(p);
		if(p+n > e)
			return "broken signature block";
		if(id == 0x7109871a){ /* V2 */
			p += 4;
			break;
		}
		p += n;
	}
	if(p == e)
		return "couldnt find v2 scheme";

	errstr = "broken scheme block";
	if(p+4 > e)
		return errstr;
	n = GET32(p), p += 4;
	if(p+n > e)
		return errstr;
	e = p+n;
	found = 0;
	while(p < e){
		n = GET32(p), p += 4;
		if(p+n > e)
			return "broken scheme block";
		errstr = parsesigner(file, trusted, p, p+n, &found);
		if(errstr != NULL)
			return errstr;
		p += n;
	}
	if(!found)
		return "no matching signer";
	return NULL;
}

const char *
verifyapk(const char *filename, X509 *trusted)
{
	Filectx file;
	struct stat st;
	const char *errstr;
	uint8_t buf[32768];
	off_t eocdoff;

	file.fd = open(filename, O_RDONLY);
	if(file.fd == -1)
		goto ferr;

	/* ignore EOCDs with comments to keep it simple, theres likely no apk like that */
	eocdoff = lseek(file.fd, -sizeof(file.eocd), SEEK_END);
	if(eocdoff == -1)
		goto ferr;
	if(read(file.fd, file.eocd, sizeof(file.eocd)) != sizeof(file.eocd))
		goto ferr;
	errstr = "couldnt find eocd, not a zip?";
	if(GET32(file.eocd) != 0x06054b50)
		goto err;
	if(GET16(file.eocd+20) != 0)
		goto err;

	errstr = "couldnt find cd";
	file.cdsize = GET32(file.eocd+12);
	file.cdoff = GET32(file.eocd+16);
	if(file.cdoff == 0xFFFFFFFF || file.cdsize == 0xFFFFFFFF)
		goto err;
	if(file.cdoff+file.cdsize != eocdoff)
		goto err;

	if(lseek(file.fd, file.cdoff-24, SEEK_SET) == -1)
		goto ferr;
	if(read(file.fd, buf, 24) != 24)
		goto ferr;
	errstr = "couldnt find signature block";
	if(memcmp(buf+8, "APK Sig Block 42", 16) != 0)
		goto err;
	file.sblksize = GET64(buf);
	errstr = "buffer is small for the signature block";
	if(file.sblksize > sizeof(buf))
		goto err;

	file.sblkoff = file.cdoff-file.sblksize-8;
	if(lseek(file.fd, file.sblkoff, SEEK_SET) == -1)
		goto ferr;
	if(read(file.fd, buf, 8) != 8)
		goto ferr;
	errstr = "invalid signature block size";
	if(file.sblksize != GET64(buf))
		goto err;
	PUT32(file.eocd+16, file.sblkoff); /* for the digest, see the spec */
	if(read(file.fd, buf, file.sblksize) != file.sblksize)
		goto ferr;

	if(fstat(file.fd, &st) != 0)
		goto ferr;
	file.filesize = st.st_size;

	errstr = parsesignblk(&file, trusted, buf);
	goto err;
ferr:
	errstr = strerror(errno);
err:
	close(file.fd);
	return errstr;
}

