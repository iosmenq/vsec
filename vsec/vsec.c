/*
 * vsec.c
 * Coded by iosmen (c) 2025
 *
 * - Supports JSON-based AES-256-CTR + HMAC-SHA256 vsec format and a small legacy fallback.
 * - Uses only Apple frameworks: CommonCrypto + Security + CoreFoundation
 * - DEK wrapping: PBKDF2 (passphrase + exe_hash) and RSA-OAEP
 * - Optional header signing: RSA-PSS-SHA256
 *
 * Build:
 *   clang -O2 -Wall -Wextra -o vsec vsec.c -framework Security -framework CoreFoundation
 *
 * Notes:
 * - This file contains fixes for:
 *     * robust base64 decoding (ignores whitespace/newlines)
 *     * initialization of all pointers to avoid "sometimes-uninitialized" warnings
 *     * safe memory handling and single-point header write (no extra bytes)
 * - Keep secrets zeroed where practical.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <unistd.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <errno.h>

#include <CoreFoundation/CoreFoundation.h>
#include <Security/Security.h>
#include <CommonCrypto/CommonCrypto.h>
#include <CommonCrypto/CommonRandom.h>
#include <CommonCrypto/CommonKeyDerivation.h>
#include <CommonCrypto/CommonHMAC.h>
#include <CommonCrypto/CommonCryptor.h>

#define MAGIC "VSECv001"
#define MAGIC_LEN 8
#define HEADER_MAX 131072
#define SALT_LEN 16
#define IV_LEN 16      /* AES block size for CTR */
#define TAG_LEN 32     /* HMAC-SHA256 */
#define DEK_LEN 32
#define PBKDF2_ITER 150000

/* ---------- helpers ---------- */

#define SAFE_FREE(p) do { if ((p) != NULL) { free(p); (p)=NULL; } } while(0)

/* write big-endian 64-bit */
static void write_be64(FILE *f, uint64_t v) {
    unsigned char b[8];
    for (int i = 7; i >= 0; --i) { b[i] = v & 0xff; v >>= 8; }
    fwrite(b, 1, 8, f);
}

static uint64_t read_be64(const unsigned char *b) {
    uint64_t v = 0;
    for (int i = 0; i < 8; ++i) v = (v << 8) | (b[i] & 0xff);
    return v;
}

/* ---------- robust base64 (ignores whitespace and non-b64 chars) ---------- */

static int b64_map(char c) {
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a' + 26;
    if (c >= '0' && c <= '9') return c - '0' + 52;
    if (c == '+') return 62;
    if (c == '/') return 63;
    if (c == '=') return -1; /* padding */
    return -2; /* ignore (whitespace/newline/other) */
}

/* return malloc'd buffer, set out_len; returns NULL on parse error */
static uint8_t *b64_decode(const char *in, size_t *out_len) {
    if (!in) return NULL;
    size_t n = strlen(in);
    /* first strip all non-base64 (whitespace etc.) */
    char *clean = malloc(n + 1);
    if (!clean) return NULL;
    size_t ci = 0;
    for (size_t i = 0; i < n; ++i) {
        int m = b64_map(in[i]);
        if (m != -2) clean[ci++] = in[i]; /* keep base64 or '=' */
    }
    clean[ci] = '\0';
    if (ci % 4 != 0) {
        /* invalid base64 length */
        SAFE_FREE(clean);
        return NULL;
    }
    size_t padding = 0;
    if (ci >= 1 && clean[ci-1] == '=') padding++;
    if (ci >= 2 && clean[ci-2] == '=') padding++;
    size_t outl = (ci / 4) * 3 - padding;
    uint8_t *out = malloc(outl ? outl : 1);
    if (!out) { SAFE_FREE(clean); return NULL; }
    size_t j = 0;
    for (size_t i = 0; i < ci; i += 4) {
        int v0 = b64_map(clean[i]);
        int v1 = b64_map(clean[i+1]);
        int v2 = b64_map(clean[i+2]);
        int v3 = b64_map(clean[i+3]);
        if (v0 < 0 || v1 < 0) { SAFE_FREE(clean); SAFE_FREE(out); return NULL; }
        int a = (v0 << 18) | (v1 << 12);
        if (clean[i+2] != '=') {
            if (v2 < 0) { SAFE_FREE(clean); SAFE_FREE(out); return NULL; }
            a |= (v2 << 6);
        }
        if (clean[i+3] != '=') {
            if (v3 < 0) { SAFE_FREE(clean); SAFE_FREE(out); return NULL; }
            a |= v3;
        }
        out[j++] = (a >> 16) & 0xFF;
        if (clean[i+2] != '=') {
            out[j++] = (a >> 8) & 0xFF;
        }
        if (clean[i+3] != '=') {
            out[j++] = a & 0xFF;
        }
    }
    SAFE_FREE(clean);
    *out_len = j;
    return out;
}

/* base64 encode (simple) */
static const char b64_table[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
static char *b64_encode(const uint8_t *data, size_t len) {
    if (!data && len) return NULL;
    size_t out_len = ((len + 2) / 3) * 4;
    char *out = malloc(out_len + 1);
    if (!out) return NULL;
    char *p = out;
    for (size_t i = 0; i < len; i += 3) {
        uint32_t v = data[i] << 16;
        if (i + 1 < len) v |= data[i+1] << 8;
        if (i + 2 < len) v |= data[i+2];
        *p++ = b64_table[(v >> 18) & 0x3F];
        *p++ = b64_table[(v >> 12) & 0x3F];
        *p++ = (i + 1 < len) ? b64_table[(v >> 6) & 0x3F] : '=';
        *p++ = (i + 2 < len) ? b64_table[v & 0x3F] : '=';
    }
    *p = '\0';
    return out;
}

/* ---------- file helpers ---------- */

static unsigned char *read_file(const char *path, size_t *out_len) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return NULL; }
    long sz = ftell(f);
    if (sz < 0) { fclose(f); return NULL; }
    rewind(f);
    unsigned char *buf = malloc((size_t)sz + 1);
    if (!buf) { fclose(f); return NULL; }
    if (fread(buf, 1, sz, f) != (size_t)sz) { free(buf); fclose(f); return NULL; }
    buf[sz] = '\0';
    fclose(f);
    *out_len = (size_t)sz;
    return buf;
}

static int write_file(const char *path, const unsigned char *data, size_t len) {
    FILE *f = fopen(path, "wb");
    if (!f) return -1;
    if (fwrite(data, 1, len, f) != len) { fclose(f); return -1; }
    fclose(f);
    return 0;
}

/* ---------- PEM -> DER tolerant helper ---------- */

static unsigned char *pem_to_der(const char *pem, size_t *out_len) {
    if (!pem) return NULL;
    size_t n = strlen(pem);
    char *b64 = malloc(n + 1);
    if (!b64) return NULL;
    size_t bi = 0;
    for (size_t i = 0; i < n; ++i) {
        char c = pem[i];
        int m = b64_map(c);
        if (m >= 0 || c == '=') b64[bi++] = c;
    }
    b64[bi] = '\0';
    unsigned char *der = b64_decode(b64, out_len);
    SAFE_FREE(b64);
    return der;
}

/* ---------- SecKey creation from DER ---------- */

static SecKeyRef seckey_from_der(const unsigned char *der, size_t der_len, int is_public) {
    if (!der || der_len == 0) return NULL;
    CFDataRef keyData = CFDataCreate(NULL, der, (CFIndex)der_len);
    if (!keyData) return NULL;
    CFStringRef keyType = kSecAttrKeyTypeRSA;
    int keySize = 2048;
    CFNumberRef keySizeNum = CFNumberCreate(NULL, kCFNumberIntType, &keySize);
    const void *keys[] = { kSecAttrKeyType, kSecAttrKeyClass, kSecAttrKeySizeInBits };
    CFStringRef keyClass = is_public ? kSecAttrKeyClassPublic : kSecAttrKeyClassPrivate;
    const void *values[] = { keyType, keyClass, keySizeNum };
    CFDictionaryRef attrs = CFDictionaryCreate(NULL, keys, values, 3,
                                               &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);
    CFErrorRef error = NULL;
    SecKeyRef key = SecKeyCreateWithData(keyData, attrs, &error);
    if (error) CFRelease(error);
    if (keySizeNum) CFRelease(keySizeNum);
    if (attrs) CFRelease(attrs);
    if (keyData) CFRelease(keyData);
    return key;
}

/* ---------- PEM loader ---------- */

static SecKeyRef load_pem_key(const char *path, int is_public) {
    size_t len;
    unsigned char *buf = read_file(path, &len);
    if (!buf) return NULL;
    unsigned char *der = NULL;
    size_t der_len = 0;
    if (strstr((char*)buf, "-----BEGIN") != NULL) {
        der = pem_to_der((const char*)buf, &der_len);
        SAFE_FREE(buf);
        if (!der) return NULL;
    } else {
        der = buf;
        der_len = len;
    }
    SecKeyRef key = seckey_from_der(der, der_len, is_public);
    if (der != buf) SAFE_FREE(der);
    else SAFE_FREE(buf);
    return key;
}

/* ---------- sha256 of file ---------- */

static int sha256_of_file_path(const char *path, unsigned char out[CC_SHA256_DIGEST_LENGTH]) {
    size_t len;
    unsigned char *buf = read_file(path, &len);
    if (!buf) return -1;
    CC_SHA256(buf, (CC_LONG)len, out);
    SAFE_FREE(buf);
    return 0;
}

/* ---------- AES-CTR encrypt/decrypt ---------- */

static int aes_ctr_crypt(const uint8_t key[32],
                         const uint8_t iv[IV_LEN],
                         const uint8_t *in, size_t in_len,
                         uint8_t **out, size_t *out_len) {
    if (!key || !iv || (!in && in_len)) return -1;
    CCCryptorRef cryptor = NULL;
    CCCryptorStatus st = CCCryptorCreateWithMode(kCCEncrypt, kCCModeCTR, kCCAlgorithmAES, ccNoPadding,
                                                 iv, key, 32, NULL, 0, 0, 0, &cryptor);
    if (st != kCCSuccess || !cryptor) return -1;
    uint8_t *buf = malloc(in_len ? in_len : 1);
    if (!buf) { CCCryptorRelease(cryptor); return -1; }
    size_t written = 0;
    st = CCCryptorUpdate(cryptor, in, in_len, buf, in_len ? in_len : 1, &written);
    CCCryptorRelease(cryptor);
    if (st != kCCSuccess || written != in_len) { free(buf); return -1; }
    *out = buf;
    *out_len = written;
    return 0;
}

/* ---------- derive two keys from DEK ---------- */

static void derive_keys_from_dek(const uint8_t dek[DEK_LEN], uint8_t aes_key[32], uint8_t mac_key[32]) {
    const char *label_enc = "enc";
    const char *label_mac = "mac";
    CCHmac(kCCHmacAlgSHA256, dek, DEK_LEN, label_enc, strlen(label_enc), aes_key);
    CCHmac(kCCHmacAlgSHA256, dek, DEK_LEN, label_mac, strlen(label_mac), mac_key);
}

/* ---------- RSA OAEP and RSA-PSS helpers ---------- */

static unsigned char *rsa_oaep_encrypt_with_key(SecKeyRef pubkey, const unsigned char *in, size_t inlen, size_t *outlen) {
    if (!pubkey) return NULL;
    CFErrorRef error = NULL;
    CFDataRef plain = CFDataCreate(NULL, in, (CFIndex)inlen);
    CFDataRef ct = SecKeyCreateEncryptedData(pubkey, kSecKeyAlgorithmRSAEncryptionOAEPSHA256, plain, &error);
    CFRelease(plain);
    if (!ct) { if (error) CFRelease(error); return NULL; }
    CFIndex clen = CFDataGetLength(ct);
    unsigned char *out = malloc((size_t)clen);
    if (!out) { CFRelease(ct); return NULL; }
    CFDataGetBytes(ct, CFRangeMake(0, clen), out);
    CFRelease(ct);
    *outlen = (size_t)clen;
    return out;
}

static unsigned char *rsa_oaep_decrypt_with_key(SecKeyRef privkey, const unsigned char *in, size_t inlen, size_t *outlen) {
    if (!privkey) return NULL;
    CFErrorRef error = NULL;
    CFDataRef ct = CFDataCreate(NULL, in, (CFIndex)inlen);
    CFDataRef plain = SecKeyCreateDecryptedData(privkey, kSecKeyAlgorithmRSAEncryptionOAEPSHA256, ct, &error);
    CFRelease(ct);
    if (!plain) { if (error) CFRelease(error); return NULL; }
    CFIndex plen = CFDataGetLength(plain);
    unsigned char *out = malloc((size_t)plen);
    if (!out) { CFRelease(plain); return NULL; }
    CFDataGetBytes(plain, CFRangeMake(0, plen), out);
    CFRelease(plain);
    *outlen = (size_t)plen;
    return out;
}

static unsigned char *rsa_pss_sign_with_key(SecKeyRef privkey, const unsigned char *data, size_t datalen, size_t *siglen) {
    if (!privkey) return NULL;
    CFErrorRef error = NULL;
    CFDataRef msg = CFDataCreate(NULL, data, (CFIndex)datalen);
    CFDataRef sig = SecKeyCreateSignature(privkey, kSecKeyAlgorithmRSASignatureMessagePSSSHA256, msg, &error);
    CFRelease(msg);
    if (!sig) { if (error) CFRelease(error); return NULL; }
    CFIndex sl = CFDataGetLength(sig);
    unsigned char *out = malloc((size_t)sl);
    if (!out) { CFRelease(sig); return NULL; }
    CFDataGetBytes(sig, CFRangeMake(0, sl), out);
    CFRelease(sig);
    *siglen = (size_t)sl;
    return out;
}

static int rsa_pss_verify_with_key(SecKeyRef pubkey, const unsigned char *data, size_t datalen, const unsigned char *sig, size_t siglen) {
    if (!pubkey) return 0;
    CFErrorRef error = NULL;
    CFDataRef msg = CFDataCreate(NULL, data, (CFIndex)datalen);
    CFDataRef sdata = CFDataCreate(NULL, sig, (CFIndex)siglen);
    Boolean ok = SecKeyVerifySignature(pubkey, kSecKeyAlgorithmRSASignatureMessagePSSSHA256, msg, sdata, &error);
    CFRelease(msg); CFRelease(sdata);
    if (!ok) { if (error) CFRelease(error); return 0; }
    return 1;
}

/* ---------- CLI ---------- */

struct options {
    int encrypt;
    int decrypt;
    const char *infile;
    const char *outfile;
    const char *passphrase;
    const char *pubkey_path;
    const char *privkey_path;
    const char *signpriv_path;
    const char *verifypub_path;
    const char *argv0;
};

static void usage(const char *prog) {
    fprintf(stderr,
        "vsec - professional .vsec encrypt/decrypt (fixed)\n\n"
        "Usage (encrypt):\n"
        "  %s -e -in plaintext -out output.vsec -pass <pass> [-pub recipient_pub.pem] [-signpriv signer_priv.pem]\n\n"
        "Usage (decrypt):\n"
        "  %s -d -in input.vsec -out plaintext -pass <pass> [-priv recipient_priv.pem] [-verifypub signer_pub.pem]\n\n"
        "Options:\n"
        "  -e              Encrypt mode\n"
        "  -d              Decrypt mode\n"
        "  -in <file>      Input file\n"
        "  -out <file>     Output file\n"
        "  -pass <pass>    Passphrase (for symmetric wrap)\n"
        "  -pub <file>     Recipient RSA public key (PEM/DER)\n"
        "  -priv <file>    Recipient RSA private key (PEM/DER)\n"
        "  -signpriv <file> Signer RSA private key (PEM/DER)\n"
        "  -verifypub <file> Signer RSA public key (PEM/DER)\n\n",
        prog, prog);
}

/* ---------- main ---------- */

int main(int argc, char **argv) {
    struct options opt = {0};
    opt.argv0 = argv[0];
    for (int i=1;i<argc;i++){
        if (!strcmp(argv[i], "-e")) opt.encrypt = 1;
        else if (!strcmp(argv[i], "-d")) opt.decrypt = 1;
        else if (!strcmp(argv[i], "-in") && i+1<argc) opt.infile = argv[++i];
        else if (!strcmp(argv[i], "-out") && i+1<argc) opt.outfile = argv[++i];
        else if (!strcmp(argv[i], "-pass") && i+1<argc) opt.passphrase = argv[++i];
        else if (!strcmp(argv[i], "-pub") && i+1<argc) opt.pubkey_path = argv[++i];
        else if (!strcmp(argv[i], "-priv") && i+1<argc) opt.privkey_path = argv[++i];
        else if (!strcmp(argv[i], "-signpriv") && i+1<argc) opt.signpriv_path = argv[++i];
        else if (!strcmp(argv[i], "-verifypub") && i+1<argc) opt.verifypub_path = argv[++i];
        else { fprintf(stderr, "Unknown arg: %s\n", argv[i]); usage(argv[0]); return 1; }
    }

    if ((opt.encrypt && opt.decrypt) || (!opt.encrypt && !opt.decrypt)) {
        fprintf(stderr, "Specify -e or -d.\n"); usage(argv[0]); return 1;
    }
    if (!opt.infile || !opt.outfile) { fprintf(stderr, "Input and output required.\n"); usage(argv[0]); return 1; }

    /* exe path (best-effort) for binding */
    char exe_path[4096] = {0};
#ifdef __linux__
    ssize_t r = readlink("/proc/self/exe", exe_path, sizeof(exe_path)-1);
    if (r > 0) exe_path[r] = '\0';
#else
    if (opt.argv0 && opt.argv0[0]) strncpy(exe_path, opt.argv0, sizeof(exe_path)-1);
#endif
    unsigned char exe_hash[CC_SHA256_DIGEST_LENGTH];
    memset(exe_hash, 0, sizeof(exe_hash));
    if (exe_path[0]) {
        if (sha256_of_file_path(exe_path, exe_hash) != 0) {
            fprintf(stderr, "Warning: cannot compute executable hash; binary-binding weaker.\n");
            memset(exe_hash, 0, sizeof(exe_hash));
        }
    }

    if (opt.encrypt) {
        /* Read plaintext */
        size_t plain_len;
        unsigned char *plain = read_file(opt.infile, &plain_len);
        if (!plain) { fprintf(stderr, "Failed to read input.\n"); return 1; }

        /* Generate DEK */
        uint8_t dek[DEK_LEN];
        if (CCRandomGenerateBytes(dek, DEK_LEN) != kCCSuccess) { fprintf(stderr, "RAND failed.\n"); SAFE_FREE(plain); return 1; }

        /* Derive content keys from DEK */
        uint8_t aes_key[32], mac_key[32];
        derive_keys_from_dek(dek, aes_key, mac_key);

        /* Encrypt content (AES-CTR) */
        uint8_t iv_file[IV_LEN];
        if (CCRandomGenerateBytes(iv_file, IV_LEN) != kCCSuccess) { fprintf(stderr, "RAND failed.\n"); SAFE_FREE(plain); return 1; }
        uint8_t *ciphertext = NULL;
        size_t ciphertext_len = 0;
        if (aes_ctr_crypt(aes_key, iv_file, plain, plain_len, &ciphertext, &ciphertext_len) != 0) {
            fprintf(stderr, "Encryption failed.\n"); SAFE_FREE(plain); return 1;
        }
        SAFE_FREE(plain);

        /* Compute HMAC tag over iv||ciphertext */
        uint8_t *hmac_input = malloc(IV_LEN + ciphertext_len);
        if (!hmac_input) { SAFE_FREE(ciphertext); return 1; }
        memcpy(hmac_input, iv_file, IV_LEN);
        memcpy(hmac_input + IV_LEN, ciphertext, ciphertext_len);
        uint8_t tag[TAG_LEN];
        CCHmac(kCCHmacAlgSHA256, mac_key, sizeof(mac_key), hmac_input, IV_LEN + ciphertext_len, tag);
        SAFE_FREE(hmac_input);

        /* Symmetric wrap DEK with KEK from passphrase+exe_hash via PBKDF2 */
        uint8_t salt[SALT_LEN];
        if (CCRandomGenerateBytes(salt, SALT_LEN) != kCCSuccess) { SAFE_FREE(ciphertext); return 1; }
        if (!opt.passphrase) { fprintf(stderr, "Encrypt requires -pass <passphrase>.\n"); SAFE_FREE(ciphertext); return 1; }
        size_t passlen = strlen(opt.passphrase);
        uint8_t *kdf_input = malloc(passlen + CC_SHA256_DIGEST_LENGTH);
        if (!kdf_input) { SAFE_FREE(ciphertext); return 1; }
        memcpy(kdf_input, opt.passphrase, passlen);
        memcpy(kdf_input + passlen, exe_hash, CC_SHA256_DIGEST_LENGTH);
        uint8_t kek[32];
        if (CCKeyDerivationPBKDF(kCCPBKDF2, (const char*)kdf_input, (int)(passlen + CC_SHA256_DIGEST_LENGTH),
                                salt, SALT_LEN, kCCPRFHmacAlgSHA256, PBKDF2_ITER, kek, sizeof(kek)) != kCCSuccess) {
            fprintf(stderr, "PBKDF2 failed.\n"); SAFE_FREE(ciphertext); SAFE_FREE(kdf_input); return 1;
        }
        SAFE_FREE(kdf_input);

        /* Wrap DEK symmetrically */
        uint8_t dek_aes[32], dek_mac[32];
        CCHmac(kCCHmacAlgSHA256, kek, sizeof(kek), "dek_enc", 7, dek_aes);
        CCHmac(kCCHmacAlgSHA256, kek, sizeof(kek), "dek_mac", 7, dek_mac);

        uint8_t iv_dek[IV_LEN];
        if (CCRandomGenerateBytes(iv_dek, IV_LEN) != kCCSuccess) { SAFE_FREE(ciphertext); return 1; }
        uint8_t *enc_dek_sym = NULL; size_t enc_dek_sym_len = 0;
        if (aes_ctr_crypt(dek_aes, iv_dek, dek, DEK_LEN, &enc_dek_sym, &enc_dek_sym_len) != 0) {
            fprintf(stderr, "DEK symmetric wrap failed.\n"); SAFE_FREE(ciphertext); return 1;
        }
        uint8_t *h_in = malloc(IV_LEN + enc_dek_sym_len);
        if (!h_in) { SAFE_FREE(ciphertext); SAFE_FREE(enc_dek_sym); return 1; }
        memcpy(h_in, iv_dek, IV_LEN);
        memcpy(h_in + IV_LEN, enc_dek_sym, enc_dek_sym_len);
        uint8_t tag_dek[TAG_LEN];
        CCHmac(kCCHmacAlgSHA256, dek_mac, sizeof(dek_mac), h_in, IV_LEN + enc_dek_sym_len, tag_dek);
        SAFE_FREE(h_in);

        /* Asymmetric wrap DEK with recipient public key if provided */
        unsigned char *enc_dek_rsa = NULL; size_t enc_dek_rsa_len = 0;
        if (opt.pubkey_path) {
            SecKeyRef pub = load_pem_key(opt.pubkey_path, 1);
            if (!pub) { fprintf(stderr, "Failed to load recipient public key.\n"); SAFE_FREE(ciphertext); SAFE_FREE(enc_dek_sym); return 1; }
            enc_dek_rsa = rsa_oaep_encrypt_with_key(pub, dek, DEK_LEN, &enc_dek_rsa_len);
            CFRelease(pub);
            if (!enc_dek_rsa) { fprintf(stderr, "RSA-OAEP wrap failed.\n"); SAFE_FREE(ciphertext); SAFE_FREE(enc_dek_sym); return 1; }
        }

        /* Build JSON header */
        char *b64_iv_file = b64_encode(iv_file, IV_LEN);
        char *b64_tag_file = b64_encode(tag, TAG_LEN);
        char *b64_iv_dek = b64_encode(iv_dek, IV_LEN);
        char *b64_tag_dek = b64_encode(tag_dek, TAG_LEN);
        char *b64_salt = b64_encode(salt, SALT_LEN);
        char *b64_enc_dek_sym = b64_encode(enc_dek_sym, (int)enc_dek_sym_len);
        char *b64_enc_dek_rsa = NULL;
        if (enc_dek_rsa) b64_enc_dek_rsa = b64_encode(enc_dek_rsa, (int)enc_dek_rsa_len);

        char exe_hash_hex[CC_SHA256_DIGEST_LENGTH*2 + 1];
        for (int i=0;i<CC_SHA256_DIGEST_LENGTH;i++) sprintf(exe_hash_hex + i*2, "%02x", exe_hash[i]);
        exe_hash_hex[CC_SHA256_DIGEST_LENGTH*2] = '\0';

        char header_json[HEADER_MAX];
        if (b64_enc_dek_rsa) {
            snprintf(header_json, sizeof(header_json),
                "{"
                "\"version\":\"1\","
                "\"cipher\":\"AES-256-CTR-HMAC-SHA256\","
                "\"iv_file\":\"%s\",\"tag_file\":\"%s\","
                "\"dek_wrap_sym\":{\"salt\":\"%s\",\"iter\":%d,\"iv\":\"%s\",\"tag\":\"%s\",\"blob\":\"%s\"},"
                "\"dek_wrap_rsa\":{\"blob\":\"%s\"},"
                "\"exe_hash\":\"%s\""
                "}",
                b64_iv_file, b64_tag_file, b64_salt, PBKDF2_ITER, b64_iv_dek, b64_tag_dek, b64_enc_dek_sym,
                b64_enc_dek_rsa, exe_hash_hex
            );
        } else {
            snprintf(header_json, sizeof(header_json),
                "{"
                "\"version\":\"1\","
                "\"cipher\":\"AES-256-CTR-HMAC-SHA256\","
                "\"iv_file\":\"%s\",\"tag_file\":\"%s\","
                "\"dek_wrap_sym\":{\"salt\":\"%s\",\"iter\":%d,\"iv\":\"%s\",\"tag\":\"%s\",\"blob\":\"%s\"},"
                "\"dek_wrap_rsa\":null,"
                "\"exe_hash\":\"%s\""
                "}",
                b64_iv_file, b64_tag_file, b64_salt, PBKDF2_ITER, b64_iv_dek, b64_tag_dek, b64_enc_dek_sym,
                exe_hash_hex
            );
        }

        /* Optionally sign header */
        char *b64_signature = NULL;
        if (opt.signpriv_path) {
            SecKeyRef signpriv = load_pem_key(opt.signpriv_path, 0);
            if (!signpriv) { fprintf(stderr, "Failed to load signer private key.\n"); goto cleanup_encrypt; }
            size_t siglen = 0;
            unsigned char *sig = rsa_pss_sign_with_key(signpriv, (unsigned char*)header_json, strlen(header_json), &siglen);
            CFRelease(signpriv);
            if (!sig) { fprintf(stderr, "Header signing failed.\n"); goto cleanup_encrypt; }
            b64_signature = b64_encode(sig, (int)siglen);
            SAFE_FREE(sig);
            if (!b64_signature) { fprintf(stderr, "Signature base64 failed.\n"); goto cleanup_encrypt; }
        }

        char final_header[HEADER_MAX];
        if (b64_signature) {
            snprintf(final_header, sizeof(final_header), "{ \"header\": %s, \"signature\":\"%s\" }", header_json, b64_signature);
        } else {
            snprintf(final_header, sizeof(final_header), "{ \"header\": %s, \"signature\": null }", header_json);
        }

        /* Write output: MAGIC | header_len(8BE) | header | ciphertext
           Ensure we write exactly these bytes in order and nothing else. */
        FILE *out = fopen(opt.outfile, "wb");
        if (!out) { fprintf(stderr, "Cannot open output file.\n"); goto cleanup_encrypt; }
        if (fwrite(MAGIC, 1, MAGIC_LEN, out) != MAGIC_LEN) { fprintf(stderr, "Write failed (magic).\n"); fclose(out); goto cleanup_encrypt; }
        uint64_t hlen = (uint64_t)strlen(final_header);
        write_be64(out, hlen);
        if (fwrite(final_header, 1, (size_t)hlen, out) != (size_t)hlen) { fprintf(stderr, "Write failed (header).\n"); fclose(out); goto cleanup_encrypt; }
        if (fwrite(ciphertext, 1, ciphertext_len, out) != ciphertext_len) { fprintf(stderr, "Write failed (ciphertext).\n"); fclose(out); goto cleanup_encrypt; }
        /* flush and close */
        fflush(out);
        fclose(out);
        fprintf(stdout, "Encryption complete: %s\n", opt.outfile);

    cleanup_encrypt:
        /* free everything safely */
        SAFE_FREE(ciphertext);
        SAFE_FREE(enc_dek_sym);
        SAFE_FREE(enc_dek_rsa);
        SAFE_FREE(b64_iv_file); SAFE_FREE(b64_tag_file);
        SAFE_FREE(b64_iv_dek); SAFE_FREE(b64_tag_dek);
        SAFE_FREE(b64_salt); SAFE_FREE(b64_enc_dek_sym); SAFE_FREE(b64_enc_dek_rsa);
        SAFE_FREE(b64_signature);
        /* zero sensitive (best-effort) */
        memset(dek, 0, sizeof(dek));
        memset(aes_key, 0, sizeof(aes_key));
        memset(mac_key, 0, sizeof(mac_key));
        memset(kek, 0, sizeof(kek));
        return 0;
    } else {
        /* Decrypt flow */
        FILE *f = fopen(opt.infile, "rb");
        if (!f) { fprintf(stderr, "Cannot open input file.\n"); return 1; }
        unsigned char magic[MAGIC_LEN];
        if (fread(magic, 1, MAGIC_LEN, f) != MAGIC_LEN) { fclose(f); fprintf(stderr, "Invalid file (magic read failed).\n"); return 1; }
        if (memcmp(magic, MAGIC, MAGIC_LEN) != 0) { fclose(f); fprintf(stderr, "Not a VSEC file (magic mismatch).\n"); return 1; }
        unsigned char be8[8];
        if (fread(be8, 1, 8, f) != 8) { fclose(f); fprintf(stderr, "Truncated file (header len read failed).\n"); return 1; }
        uint64_t header_len = read_be64(be8);
        if (header_len == 0 || header_len > HEADER_MAX) { fclose(f); fprintf(stderr, "Invalid header length.\n"); return 1; }
        char *header_buf = malloc((size_t)header_len + 1);
        if (!header_buf) { fclose(f); fprintf(stderr, "Memory error (header alloc).\n"); return 1; }
        if (fread(header_buf, 1, (size_t)header_len, f) != (size_t)header_len) { SAFE_FREE(header_buf); fclose(f); fprintf(stderr, "Failed to read header.\n"); return 1; }
        header_buf[header_len] = '\0';
        long cur = ftell(f);
        fseek(f, 0, SEEK_END);
        long end = ftell(f);
        if (end < 0) { SAFE_FREE(header_buf); fclose(f); fprintf(stderr, "ftell error.\n"); return 1; }
        /* ciphertext length = file_end - current_offset */
        size_t ciph_len = (size_t)(end - cur);
        fseek(f, cur, SEEK_SET);
        unsigned char *cipher_rest = NULL;
        if (ciph_len) {
            cipher_rest = malloc(ciph_len);
            if (!cipher_rest) { SAFE_FREE(header_buf); fclose(f); fprintf(stderr, "Memory error (cipher alloc).\n"); return 1; }
            if (fread(cipher_rest, 1, ciph_len, f) != ciph_len) { SAFE_FREE(header_buf); SAFE_FREE(cipher_rest); fclose(f); fprintf(stderr, "Failed to read ciphertext.\n"); return 1; }
        }
        fclose(f);

        /* Determine JSON style */
        int header_is_json = 0;
        if (header_buf[0] == '{' || strstr(header_buf, "\"cipher\"")) header_is_json = 1;

        /* initialize variables that will be used below */
        char *sig_b64 = NULL;
        char *header_obj = NULL;
        char *iv_file_b64 = NULL, *tag_file_b64 = NULL, *salt_b64 = NULL, *iv_dek_b64 = NULL, *tag_dek_b64 = NULL, *enc_dek_sym_b64 = NULL, *enc_dek_rsa_b64 = NULL, *exe_hash_hex = NULL;

        if (!header_is_json) {
            /* legacy fallback: treat header_buf as raw IV|TAG if length matches */
            if (header_len >= (IV_LEN + TAG_LEN)) {
                unsigned char iv_file[IV_LEN];
                unsigned char tag_file[TAG_LEN];
                memcpy(iv_file, header_buf, IV_LEN);
                memcpy(tag_file, header_buf + IV_LEN, TAG_LEN);
                if (!opt.passphrase) { fprintf(stderr, "Legacy file requires -pass.\n"); SAFE_FREE(header_buf); SAFE_FREE(cipher_rest); return 1; }
                size_t passlen = strlen(opt.passphrase);
                uint8_t *kdf_input = malloc(passlen + CC_SHA256_DIGEST_LENGTH);
                if (!kdf_input) { SAFE_FREE(header_buf); SAFE_FREE(cipher_rest); fprintf(stderr, "Memory error.\n"); return 1; }
                memcpy(kdf_input, opt.passphrase, passlen);
                memcpy(kdf_input + passlen, exe_hash, CC_SHA256_DIGEST_LENGTH);
                uint8_t kek[32];
                if (CCKeyDerivationPBKDF(kCCPBKDF2, (const char*)kdf_input, (int)(passlen + CC_SHA256_DIGEST_LENGTH),
                                        iv_file, IV_LEN, kCCPRFHmacAlgSHA256, PBKDF2_ITER, kek, sizeof(kek)) != kCCSuccess) {
                    fprintf(stderr, "PBKDF2 failed (legacy).\n"); SAFE_FREE(kdf_input); SAFE_FREE(header_buf); SAFE_FREE(cipher_rest); return 1;
                }
                SAFE_FREE(kdf_input);
                uint8_t aes_key[32], mac_key[32];
                derive_keys_from_dek(kek, aes_key, mac_key);
                /* verify HMAC */
                uint8_t *h_in = malloc(IV_LEN + ciph_len);
                if (!h_in) { SAFE_FREE(header_buf); SAFE_FREE(cipher_rest); return 1; }
                memcpy(h_in, iv_file, IV_LEN);
                if (ciph_len) memcpy(h_in + IV_LEN, cipher_rest, ciph_len);
                uint8_t calc_tag[TAG_LEN];
                CCHmac(kCCHmacAlgSHA256, mac_key, sizeof(mac_key), h_in, IV_LEN + ciph_len, calc_tag);
                SAFE_FREE(h_in);
                if (memcmp(calc_tag, tag_file, TAG_LEN) != 0) {
                    fprintf(stderr, "HMAC verification failed (legacy).\n"); SAFE_FREE(header_buf); SAFE_FREE(cipher_rest); return 1;
                }
                /* decrypt */
                uint8_t *plain_out = NULL; size_t plain_out_len = 0;
                if (aes_ctr_crypt(aes_key, iv_file, cipher_rest, ciph_len, &plain_out, &plain_out_len) != 0) {
                    fprintf(stderr, "Decryption failed (legacy).\n"); SAFE_FREE(header_buf); SAFE_FREE(cipher_rest); return 1;
                }
                if (write_file(opt.outfile, plain_out, plain_out_len) != 0) {
                    fprintf(stderr, "Failed to write output.\n"); SAFE_FREE(header_buf); SAFE_FREE(cipher_rest); SAFE_FREE(plain_out); return 1;
                }
                fprintf(stdout, "Decryption (legacy) successful: %s\n", opt.outfile);
                SAFE_FREE(plain_out);
                SAFE_FREE(header_buf);
                SAFE_FREE(cipher_rest);
                return 0;
            } else {
                fprintf(stderr, "Unknown legacy header format.\n");
                SAFE_FREE(header_buf); SAFE_FREE(cipher_rest);
                return 1;
            }
        }

        /* JSON-style header parse (minimal, tolerant) */
        char *p_sig = strstr(header_buf, "\"signature\":");
        if (p_sig) {
            char *q = strchr(p_sig, ':');
            if (q) {
                q++;
                while (*q == ' ' ) q++;
                if (*q == '\"') {
                    q++;
                    char *endq = strchr(q, '\"');
                    if (endq) {
                        size_t slen = endq - q;
                        sig_b64 = malloc(slen + 1);
                        if (sig_b64) {
                            memcpy(sig_b64, q, slen);
                            sig_b64[slen] = '\0';
                        }
                    }
                }
            }
        }

        /* extract header object substring safely */
        char *hdr_obj_start = strstr(header_buf, "\"header\":");
        if (!hdr_obj_start) { fprintf(stderr, "Malformed JSON header (missing \"header\").\n"); goto cleanup_decrypt; }
        char *p = strchr(hdr_obj_start, '{');
        if (!p) { fprintf(stderr, "Malformed header object (no '{').\n"); goto cleanup_decrypt; }
        int depth = 0;
        char *q = p;
        while (*q) {
            if (*q == '{') depth++;
            else if (*q == '}') { depth--; if (depth == 0) { q++; break; } }
            q++;
        }
        if (!q) { fprintf(stderr, "Malformed header object (unbalanced braces).\n"); goto cleanup_decrypt; }
        size_t header_obj_len = q - p;
        header_obj = malloc(header_obj_len + 1);
        if (!header_obj) { fprintf(stderr, "Memory error (header_obj).\n"); goto cleanup_decrypt; }
        memcpy(header_obj, p, header_obj_len);
        header_obj[header_obj_len] = '\0';

        /* Verify signature if present and verification key provided */
        if (sig_b64 && opt.verifypub_path) {
            size_t sig_bin_len = 0;
            unsigned char *sig_bin = b64_decode(sig_b64, &sig_bin_len);
            if (!sig_bin) { fprintf(stderr, "Malformed signature base64.\n"); SAFE_FREE(sig_bin); goto cleanup_decrypt; }
            SecKeyRef verpub = load_pem_key(opt.verifypub_path, 1);
            if (!verpub) { fprintf(stderr, "Cannot load verification public key.\n"); SAFE_FREE(sig_bin); goto cleanup_decrypt; }
            int ok = rsa_pss_verify_with_key(verpub, (unsigned char*)header_obj, header_obj_len, sig_bin, sig_bin_len);
            CFRelease(verpub);
            SAFE_FREE(sig_bin);
            if (!ok) { fprintf(stderr, "Signature verification FAILED. Aborting.\n"); goto cleanup_decrypt; }
            fprintf(stdout, "Signature verification: OK\n");
        } else {
            if (sig_b64) fprintf(stderr, "Signature present but no -verifypub provided: skipping verification.\n");
        }

        /* Extract base64 fields from header_obj (simple token search) */
        char *tmp;
        if ((tmp = strstr(header_obj, "\"iv_file\":\""))) {
            tmp += strlen("\"iv_file\":\"");
            char *endq = strchr(tmp, '"'); if (endq) {
                size_t L = endq - tmp;
                iv_file_b64 = malloc(L+1);
                if (iv_file_b64) { memcpy(iv_file_b64, tmp, L); iv_file_b64[L]=0; }
            }
        }
        if ((tmp = strstr(header_obj, "\"tag_file\":\""))) {
            tmp += strlen("\"tag_file\":\"");
            char *endq = strchr(tmp, '"'); if (endq) {
                size_t L = endq - tmp;
                tag_file_b64 = malloc(L+1);
                if (tag_file_b64) { memcpy(tag_file_b64, tmp, L); tag_file_b64[L]=0; }
            }
        }
        if ((tmp = strstr(header_obj, "\"salt\":\""))) {
            tmp += strlen("\"salt\":\"");
            char *endq = strchr(tmp, '"'); if (endq) {
                size_t L = endq - tmp;
                salt_b64 = malloc(L+1);
                if (salt_b64) { memcpy(salt_b64, tmp, L); salt_b64[L]=0; }
            }
        }
        /* dek_wrap_sym object fields */
        if ((tmp = strstr(header_obj, "\"dek_wrap_sym\":"))) {
            char *pos = strstr(header_obj, "\"dek_wrap_sym\":");
            if (pos) {
                char *p_iv = strstr(pos, "\"iv\":\"");
                if (p_iv) { p_iv += strlen("\"iv\":\""); char *endq = strchr(p_iv, '"'); if (endq) { size_t L = endq - p_iv; iv_dek_b64 = malloc(L+1); if (iv_dek_b64) { memcpy(iv_dek_b64, p_iv, L); iv_dek_b64[L]=0; } } }
                char *p_tag = strstr(pos, "\"tag\":\"");
                if (p_tag) { p_tag += strlen("\"tag\":\""); char *endq = strchr(p_tag, '"'); if (endq) { size_t L = endq - p_tag; tag_dek_b64 = malloc(L+1); if (tag_dek_b64) { memcpy(tag_dek_b64, p_tag, L); tag_dek_b64[L]=0; } } }
                char *p_blob = strstr(pos, "\"blob\":\"");
                if (p_blob) { p_blob += strlen("\"blob\":\""); char *endq = strchr(p_blob, '"'); if (endq) { size_t L = endq - p_blob; enc_dek_sym_b64 = malloc(L+1); if (enc_dek_sym_b64) { memcpy(enc_dek_sym_b64, p_blob, L); enc_dek_sym_b64[L]=0; } } }
            }
        }
        /* dek_wrap_rsa */
        if ((tmp = strstr(header_obj, "\"dek_wrap_rsa\":"))) {
            char *pos2 = strstr(header_obj, "\"dek_wrap_rsa\":");
            if (pos2) {
                char *pb = strstr(pos2, "\"blob\":\"");
                if (pb) { pb += strlen("\"blob\":\""); char *endq = strchr(pb, '"'); if (endq) { size_t L = endq - pb; enc_dek_rsa_b64 = malloc(L+1); if (enc_dek_rsa_b64) { memcpy(enc_dek_rsa_b64, pb, L); enc_dek_rsa_b64[L]=0; } } }
            }
        }
        if ((tmp = strstr(header_obj, "\"exe_hash\":\""))) {
            tmp += strlen("\"exe_hash\":\"");
            char *endq = strchr(tmp, '"'); if (endq) {
                size_t L = endq - tmp;
                exe_hash_hex = malloc(L+1);
                if (exe_hash_hex) { memcpy(exe_hash_hex, tmp, L); exe_hash_hex[L] = 0; }
            }
        }

        /* compute local exe hash to compare if exe_hash field present */
        unsigned char local_exe_hash[CC_SHA256_DIGEST_LENGTH];
        memset(local_exe_hash, 0, sizeof(local_exe_hash));
        if (exe_path[0]) {
            if (sha256_of_file_path(exe_path, local_exe_hash) == 0) {
                char local_hex[CC_SHA256_DIGEST_LENGTH*2 + 1];
                for (int i=0;i<CC_SHA256_DIGEST_LENGTH;i++) sprintf(local_hex + i*2, "%02x", local_exe_hash[i]);
                local_hex[CC_SHA256_DIGEST_LENGTH*2] = '\0';
                if (exe_hash_hex && strcmp(local_hex, exe_hash_hex) != 0) {
                    fprintf(stderr, "Warning: executable hash mismatch; binary-bound KEK may not match.\n");
                }
            } else {
                fprintf(stderr, "Warning: cannot compute executable hash locally.\n");
            }
        }

        /* Unwrap DEK: try symmetric first */
        uint8_t dek[DEK_LEN];
        int got_dek = 0;

        if (enc_dek_sym_b64 && salt_b64 && iv_dek_b64 && tag_dek_b64) {
            if (!opt.passphrase) {
                fprintf(stderr, "Symmetric wrapped DEK present: provide -pass to attempt.\n");
            } else {
                size_t salt_len=0, iv_dek_len=0, tag_dek_len=0, enc_dek_sym_len=0;
                unsigned char *salt = b64_decode(salt_b64, &salt_len);
                unsigned char *iv_dek = b64_decode(iv_dek_b64, &iv_dek_len);
                unsigned char *tag_dek = b64_decode(tag_dek_b64, &tag_dek_len);
                unsigned char *enc_dek_sym = b64_decode(enc_dek_sym_b64, &enc_dek_sym_len);
                if (!salt || !iv_dek || !tag_dek || !enc_dek_sym) {
                    fprintf(stderr, "Malformed base64 in header (DEK symmetric fields).\n");
                    SAFE_FREE(salt); SAFE_FREE(iv_dek); SAFE_FREE(tag_dek); SAFE_FREE(enc_dek_sym);
                    goto try_rsa;
                }
                size_t passlen = strlen(opt.passphrase);
                uint8_t *kdf_input = malloc(passlen + CC_SHA256_DIGEST_LENGTH);
                memcpy(kdf_input, opt.passphrase, passlen);
                memcpy(kdf_input + passlen, local_exe_hash, CC_SHA256_DIGEST_LENGTH);
                uint8_t kek[32];
                if (CCKeyDerivationPBKDF(kCCPBKDF2, (const char*)kdf_input, (int)(passlen + CC_SHA256_DIGEST_LENGTH),
                                        salt, (int)salt_len, kCCPRFHmacAlgSHA256, PBKDF2_ITER, kek, sizeof(kek)) != kCCSuccess) {
                    fprintf(stderr, "PBKDF2 failed during DEK unwrap.\n");
                } else {
                    uint8_t dek_aes[32], dek_mac[32];
                    CCHmac(kCCHmacAlgSHA256, kek, sizeof(kek), "dek_enc", 7, dek_aes);
                    CCHmac(kCCHmacAlgSHA256, kek, sizeof(kek), "dek_mac", 7, dek_mac);

                    uint8_t *tmp_in = malloc(iv_dek_len + enc_dek_sym_len);
                    if (!tmp_in) { SAFE_FREE(kdf_input); SAFE_FREE(salt); SAFE_FREE(iv_dek); SAFE_FREE(tag_dek); SAFE_FREE(enc_dek_sym); goto cleanup_decrypt; }
                    memcpy(tmp_in, iv_dek, iv_dek_len);
                    memcpy(tmp_in + iv_dek_len, enc_dek_sym, enc_dek_sym_len);
                    uint8_t calc_tag_dek[TAG_LEN];
                    CCHmac(kCCHmacAlgSHA256, dek_mac, sizeof(dek_mac), tmp_in, iv_dek_len + enc_dek_sym_len, calc_tag_dek);
                    SAFE_FREE(tmp_in);
                    if (tag_dek_len != TAG_LEN || memcmp(calc_tag_dek, tag_dek, TAG_LEN) != 0) {
                        fprintf(stderr, "DEK symmetric tag mismatch.\n");
                    } else {
                        uint8_t *dek_plain = NULL; size_t dek_plain_len = 0;
                        if (aes_ctr_crypt(dek_aes, iv_dek, enc_dek_sym, enc_dek_sym_len, &dek_plain, &dek_plain_len) == 0) {
                            if (dek_plain_len == DEK_LEN) {
                                memcpy(dek, dek_plain, DEK_LEN);
                                got_dek = 1;
                            }
                            SAFE_FREE(dek_plain);
                        } else {
                            fprintf(stderr, "DEK symmetric unwrap failed.\n");
                        }
                    }
                }
                SAFE_FREE(kdf_input);
                SAFE_FREE(salt); SAFE_FREE(iv_dek); SAFE_FREE(tag_dek); SAFE_FREE(enc_dek_sym);
            }
        }

    try_rsa:
        if (!got_dek && enc_dek_rsa_b64 && opt.privkey_path) {
            size_t enc_len=0;
            unsigned char *enc_rsa = b64_decode(enc_dek_rsa_b64, &enc_len);
            if (!enc_rsa) { fprintf(stderr, "Failed to decode RSA blob.\n"); goto cleanup_decrypt; }
            SecKeyRef priv = load_pem_key(opt.privkey_path, 0);
            if (!priv) { SAFE_FREE(enc_rsa); fprintf(stderr, "Cannot load private key.\n"); goto cleanup_decrypt; }
            size_t deklen = 0;
            unsigned char *dek_plain = rsa_oaep_decrypt_with_key(priv, enc_rsa, enc_len, &deklen);
            CFRelease(priv);
            SAFE_FREE(enc_rsa);
            if (dek_plain && deklen == DEK_LEN) {
                memcpy(dek, dek_plain, DEK_LEN);
                SAFE_FREE(dek_plain);
                got_dek = 1;
            } else {
                SAFE_FREE(dek_plain);
                fprintf(stderr, "RSA DEK unwrap failed.\n");
            }
        }

        if (!got_dek) { fprintf(stderr, "Failed to unwrap DEK. Cannot decrypt.\n"); goto cleanup_decrypt; }

        /* Derive content keys from DEK */
        uint8_t aes_key[32], mac_key[32];
        derive_keys_from_dek(dek, aes_key, mac_key);

        /* Decode iv_file and tag_file */
        size_t iv_file_len=0, tag_file_len=0;
        unsigned char *iv_file = NULL, *tag_file = NULL;
        if (iv_file_b64 && tag_file_b64) {
            iv_file = b64_decode(iv_file_b64, &iv_file_len);
            tag_file = b64_decode(tag_file_b64, &tag_file_len);
        } else {
            fprintf(stderr, "Header missing iv/tag.\n"); goto cleanup_decrypt;
        }
        if (!iv_file || !tag_file || tag_file_len != TAG_LEN || iv_file_len != IV_LEN) { fprintf(stderr, "Invalid iv/tag encoding.\n"); SAFE_FREE(iv_file); SAFE_FREE(tag_file); goto cleanup_decrypt; }

        /* Verify HMAC */
        uint8_t *h_in2 = malloc(iv_file_len + ciph_len);
        if (!h_in2) { SAFE_FREE(iv_file); SAFE_FREE(tag_file); goto cleanup_decrypt; }
        memcpy(h_in2, iv_file, iv_file_len);
        if (ciph_len) memcpy(h_in2 + iv_file_len, cipher_rest, ciph_len);
        uint8_t calc_tag[TAG_LEN];
        CCHmac(kCCHmacAlgSHA256, mac_key, sizeof(mac_key), h_in2, iv_file_len + ciph_len, calc_tag);
        SAFE_FREE(h_in2);
        if (memcmp(calc_tag, tag_file, TAG_LEN) != 0) {
            fprintf(stderr, "HMAC authentication failed. Aborting.\n"); SAFE_FREE(iv_file); SAFE_FREE(tag_file); goto cleanup_decrypt;
        }

        /* Decrypt ciphertext */
        uint8_t *plain_out = NULL; size_t plain_out_len = 0;
        if (aes_ctr_crypt(aes_key, iv_file, cipher_rest, ciph_len, &plain_out, &plain_out_len) != 0) {
            fprintf(stderr, "Decryption failed.\n"); SAFE_FREE(iv_file); SAFE_FREE(tag_file); goto cleanup_decrypt;
        }

        if (write_file(opt.outfile, plain_out, plain_out_len) != 0) {
            fprintf(stderr, "Failed to write plaintext output.\n"); SAFE_FREE(iv_file); SAFE_FREE(tag_file); SAFE_FREE(plain_out); goto cleanup_decrypt;
        }
        fprintf(stdout, "Decryption successful: %s\n", opt.outfile);
        SAFE_FREE(iv_file); SAFE_FREE(tag_file); SAFE_FREE(plain_out);

    cleanup_decrypt:
        SAFE_FREE(header_buf);
        SAFE_FREE(cipher_rest);
        SAFE_FREE(sig_b64);
        SAFE_FREE(header_obj);
        SAFE_FREE(iv_file_b64); SAFE_FREE(tag_file_b64); SAFE_FREE(salt_b64);
        SAFE_FREE(iv_dek_b64); SAFE_FREE(tag_dek_b64); SAFE_FREE(enc_dek_sym_b64); SAFE_FREE(enc_dek_rsa_b64);
        SAFE_FREE(exe_hash_hex);
        memset(dek, 0, sizeof(dek));
        return 0;
    }

    return 0;
}





