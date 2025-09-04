#include <stdint.h>
#include <stddef.h>

/*************/
/* Utilities */
/*************/

static inline void memcpy_u8(const void *out, const void *in, size_t len) {
  uint8_t *out_p, *in_p;
  out_p = (uint8_t *)out;
  in_p = (uint8_t *)in;
  for (uint64_t i = 0; i < len; i++) out_p[i] = in_p[i];
}

static inline void memset_u8(const void *out, const uint8_t v, size_t len) {
  uint8_t *out_p = (uint8_t *)out;
  for(uint64_t i = 0; i < len; i++) out_p[i] = v;
}

static inline uint64_t rotr_u64(uint64_t value, int shift) {
  return (value >> shift) | (value << ((-shift) & 63));
}

static inline uint64_t load_u64_swap_endian(const void *ptr) {
  uint64_t ret;
  memcpy_u8(&ret, ptr, sizeof(ret));
  return __builtin_bswap64(ret);
}

static inline void store_u64_swap_endian(void *out, uint64_t v) {
  v = __builtin_bswap64(v);
  memcpy_u8(out, &v, sizeof(v));
}


/***********/
/* SHA-512 */
/***********/

#define SHA512_DIGEST_LENGTH 64 // message digest length in bytes
#define SHA512_BLOCK_LENGTH 128 // block length in bytes

typedef struct {
  uint64_t h[8]; // hash buffer
  uint64_t msg_len_lo, msg_len_hi; // length of message in bits
  uint8_t cur_block [128]; // although each round uses an 8-byte word, the message may not be 8-byte aligned, so uint8_t is easier to work with
  uint8_t cur_pos; // index of the next empty position in cur_block
} sha512_ctx;
// Data structure invariant:
// After initializing, before finalizing
//  h is the state of the hash buffer after processing whole blocks of message;
//  msg_len_hi * 2^64 + msg_len_lo is the number of bits of message already processed or placed into cur_block;
//  cur_pos points to the first available position of cur_block.

const uint64_t K[80] = {
  UINT64_C(0x428a2f98d728ae22), UINT64_C(0x7137449123ef65cd),
  UINT64_C(0xb5c0fbcfec4d3b2f), UINT64_C(0xe9b5dba58189dbbc),
  UINT64_C(0x3956c25bf348b538), UINT64_C(0x59f111f1b605d019),
  UINT64_C(0x923f82a4af194f9b), UINT64_C(0xab1c5ed5da6d8118),
  UINT64_C(0xd807aa98a3030242), UINT64_C(0x12835b0145706fbe),
  UINT64_C(0x243185be4ee4b28c), UINT64_C(0x550c7dc3d5ffb4e2),
  UINT64_C(0x72be5d74f27b896f), UINT64_C(0x80deb1fe3b1696b1),
  UINT64_C(0x9bdc06a725c71235), UINT64_C(0xc19bf174cf692694),
  UINT64_C(0xe49b69c19ef14ad2), UINT64_C(0xefbe4786384f25e3),
  UINT64_C(0x0fc19dc68b8cd5b5), UINT64_C(0x240ca1cc77ac9c65),
  UINT64_C(0x2de92c6f592b0275), UINT64_C(0x4a7484aa6ea6e483),
  UINT64_C(0x5cb0a9dcbd41fbd4), UINT64_C(0x76f988da831153b5),
  UINT64_C(0x983e5152ee66dfab), UINT64_C(0xa831c66d2db43210),
  UINT64_C(0xb00327c898fb213f), UINT64_C(0xbf597fc7beef0ee4),
  UINT64_C(0xc6e00bf33da88fc2), UINT64_C(0xd5a79147930aa725),
  UINT64_C(0x06ca6351e003826f), UINT64_C(0x142929670a0e6e70),
  UINT64_C(0x27b70a8546d22ffc), UINT64_C(0x2e1b21385c26c926),
  UINT64_C(0x4d2c6dfc5ac42aed), UINT64_C(0x53380d139d95b3df),
  UINT64_C(0x650a73548baf63de), UINT64_C(0x766a0abb3c77b2a8),
  UINT64_C(0x81c2c92e47edaee6), UINT64_C(0x92722c851482353b),
  UINT64_C(0xa2bfe8a14cf10364), UINT64_C(0xa81a664bbc423001),
  UINT64_C(0xc24b8b70d0f89791), UINT64_C(0xc76c51a30654be30),
  UINT64_C(0xd192e819d6ef5218), UINT64_C(0xd69906245565a910),
  UINT64_C(0xf40e35855771202a), UINT64_C(0x106aa07032bbd1b8),
  UINT64_C(0x19a4c116b8d2d0c8), UINT64_C(0x1e376c085141ab53),
  UINT64_C(0x2748774cdf8eeb99), UINT64_C(0x34b0bcb5e19b48a8),
  UINT64_C(0x391c0cb3c5c95a63), UINT64_C(0x4ed8aa4ae3418acb),
  UINT64_C(0x5b9cca4f7763e373), UINT64_C(0x682e6ff3d6b2b8a3),
  UINT64_C(0x748f82ee5defb2fc), UINT64_C(0x78a5636f43172f60),
  UINT64_C(0x84c87814a1f0ab72), UINT64_C(0x8cc702081a6439ec),
  UINT64_C(0x90befffa23631e28), UINT64_C(0xa4506cebde82bde9),
  UINT64_C(0xbef9a3f7b2c67915), UINT64_C(0xc67178f2e372532b),
  UINT64_C(0xca273eceea26619c), UINT64_C(0xd186b8c721c0c207),
  UINT64_C(0xeada7dd6cde0eb1e), UINT64_C(0xf57d4f7fee6ed178),
  UINT64_C(0x06f067aa72176fba), UINT64_C(0x0a637dc5a2c898a6),
  UINT64_C(0x113f9804bef90dae), UINT64_C(0x1b710b35131c471b),
  UINT64_C(0x28db77f523047d84), UINT64_C(0x32caab7b40c72493),
  UINT64_C(0x3c9ebe0a15c9bebc), UINT64_C(0x431d67c49c100d4c),
  UINT64_C(0x4cc5d4becb3e42b6), UINT64_C(0x597f299cfc657e2a),
  UINT64_C(0x5fcb6fab3ad6faec), UINT64_C(0x6c44198c4a475817),
};

static inline uint64_t Sigma0(uint64_t x) {
  return rotr_u64(x, 28) ^ rotr_u64(x, 34) ^ rotr_u64(x, 39);
}

static inline uint64_t Sigma1(uint64_t x) {
  return rotr_u64(x, 14) ^ rotr_u64(x, 18) ^ rotr_u64(x, 41);
}

static inline uint64_t sigma0(uint64_t x) {
  return rotr_u64(x, 1) ^ rotr_u64(x, 8) ^ (x >> 7);
}

static inline uint64_t sigma1(uint64_t x) {
  return rotr_u64(x, 19) ^ rotr_u64(x, 61) ^ (x >> 6);
}

static inline uint64_t Ch(uint64_t x, uint64_t y, uint64_t z) {
  return (x & y) ^ (~x & z);
}

static inline uint64_t Maj(uint64_t x, uint64_t y, uint64_t z) {
  return (x & y) ^ (x & z) ^ (y & z);
}

void sha512_init(sha512_ctx *sha) {
  sha->h[0] = UINT64_C(0x6a09e667f3bcc908);
  sha->h[1] = UINT64_C(0xbb67ae8584caa73b);
  sha->h[2] = UINT64_C(0x3c6ef372fe94f82b);
  sha->h[3] = UINT64_C(0xa54ff53a5f1d36f1);
  sha->h[4] = UINT64_C(0x510e527fade682d1);
  sha->h[5] = UINT64_C(0x9b05688c2b3e6c1f);
  sha->h[6] = UINT64_C(0x1f83d9abfb41bd6b);
  sha->h[7] = UINT64_C(0x5be0cd19137e2179);

  sha->msg_len_lo = 0;
  sha->msg_len_hi = 0;
  sha->cur_pos = 0;
}

static void __attribute__ ((noinline)) msg_schedule(uint64_t schedule[80], const uint8_t *in_data) {
  for(uint64_t i = 0; i < 16; i++) {
    schedule[i] = load_u64_swap_endian(in_data + i * 8);
  }
  for(uint64_t i = 16; i < 80; i++) {
    schedule[i] = sigma1(schedule[i-2]) + schedule[i-7] \
    + sigma0(schedule[i-15]) + schedule[i-16];
  }
}

static void sha512_process_block(uint64_t h[8], const uint8_t *in_data) {
  uint64_t schedule[80];
  uint64_t a[8];
  uint64_t t1, t2;

  msg_schedule(schedule, in_data);

  // Initialization
  for(uint64_t i = 0; i < 8; i++) a[i] = h[i];

  // 80 rounds of compression
  size_t rnd = 0;
  while(rnd < 80) {
    t1 = a[7] + Sigma1(a[4]) + Ch(a[4], a[5], a[6]) \
      + K[rnd] + schedule[rnd];
    t2 = Sigma0(a[0]) + Maj(a[0], a[1], a[2]);
    for(uint64_t i = 7; i > 0; i--) a[i] = a[i-1];
    a[0] = t1 + t2;
    a[4] += t1;
    rnd++;
  }

  // Final addition into hash buffer
  for(uint64_t i = 0; i < 8; i++) h[i] += a[i];
}

static void __attribute__ ((noinline)) sha512_process_blocks(uint64_t h[8], const uint8_t *in_data, size_t num_blocks) {
  while(num_blocks--) {
    sha512_process_block(h, in_data);
    in_data += SHA512_BLOCK_LENGTH;
  }
}

void sha512_update(sha512_ctx *sha, const void *in_data, size_t in_len) {
  // Update message length
  uint64_t l = sha->msg_len_lo + (((uint64_t)in_len) << 3);
  if (l < sha->msg_len_lo) {
    sha->msg_len_hi++;
  }
  if (sizeof(in_len) >= 8) {
    sha->msg_len_hi += (((uint64_t)in_len) >> 61);
  }
  sha->msg_len_lo = l;

  // Fill up the sha->cur_block buffer as much as possible
  if (sha->cur_pos != 0) {
    size_t n = SHA512_BLOCK_LENGTH - sha->cur_pos;

    if (in_len < n) {
      memcpy_u8(sha->cur_block + sha->cur_pos, in_data, in_len);
      sha->cur_pos += (uint8_t)in_len;
      return;
    } else {
      memcpy_u8(sha->cur_block + sha->cur_pos, in_data, n);
      sha512_process_blocks(sha->h, sha->cur_block, 1);
      sha->cur_pos = 0;
      in_len -= n;
      in_data += n;
    }
  }

  // Process blocks until the message is not long enough to fill a block
  if (in_len >= SHA512_BLOCK_LENGTH) {
    sha512_process_blocks(sha->h, in_data, in_len / SHA512_BLOCK_LENGTH);
    in_data += in_len;
    in_len %= SHA512_BLOCK_LENGTH;
    in_data -= in_len;
  }

  // Put the rest of the message into the sha->cur_block buffer
  if (in_len != 0) {
    memcpy_u8(sha->cur_block, in_data, in_len);
    sha->cur_pos = (uint8_t)in_len;
  }
}

void sha512_final(uint8_t out[SHA512_DIGEST_LENGTH], sha512_ctx *sha) {
  sha->cur_block[sha->cur_pos] = 0x80;  // First byte of padding
  sha->cur_pos++;
  if (sha->cur_pos > (SHA512_BLOCK_LENGTH - 16)) {
    // Need two more blocks
    memset_u8(sha->cur_block + sha->cur_pos, 0, SHA512_BLOCK_LENGTH - sha->cur_pos);
    sha512_process_block(sha->h, sha->cur_block);
    sha->cur_pos = 0;
  }

  // Pad the final block
  memset_u8(sha->cur_block + sha->cur_pos, 0, SHA512_BLOCK_LENGTH - 16 - sha->cur_pos);

  // End with message length in bits and in big-endian
  store_u64_swap_endian(sha->cur_block + SHA512_BLOCK_LENGTH - 16, sha->msg_len_hi);
  store_u64_swap_endian(sha->cur_block + SHA512_BLOCK_LENGTH - 8, sha->msg_len_lo);

  sha512_process_block(sha->h, sha->cur_block);

  // Copy the message digest into out
  for(uint64_t i = 0; i < 8; i++) {
    store_u64_swap_endian(out + i * 8, sha->h[i]);
  }
}
