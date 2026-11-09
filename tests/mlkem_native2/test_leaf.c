/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * Tests of the new asm leaf functions (arm/mlkem) against the
 * reference: mlkem-native's portable C built with the prefix "ref". Where
 * the input space allows, each coefficient or byte position sees every
 * possible value; otherwise inputs are random. Outputs sit between guard
 * bytes, which must survive, and inputs must be unchanged.
 *
 * Functions missing from the link (weak symbols) are skipped.
 *
 * usage: test_leaf [RANDOM_TESTS [NAME]]   (default 10000, all)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define Q 3329
#define WEAK __attribute__((weak))

typedef struct
{
  int16_t coeffs[256];
} __attribute__((aligned(32))) poly;

/* The reference */
void ref_poly_cbd2(poly *r, const uint8_t buf[128]);
void ref_poly_cbd3(poly *r, const uint8_t buf[192]);

void ref_poly_compress_d4(uint8_t *r, const poly *a);
void ref_poly_compress_d5(uint8_t *r, const poly *a);
void ref_poly_compress_d10(uint8_t *r, const poly *a);
void ref_poly_compress_d11(uint8_t *r, const poly *a);
void ref_poly_decompress_d4(poly *r, const uint8_t *a);
void ref_poly_decompress_d5(poly *r, const uint8_t *a);
void ref_poly_decompress_d10(poly *r, const uint8_t *a);
void ref_poly_decompress_d11(poly *r, const uint8_t *a);

void ref_poly_frommsg(poly *r, const uint8_t msg[32]);
void ref_poly_tomsg(uint8_t msg[32], const poly *a);

void ref_poly_frombytes(poly *r, const uint8_t a[384]);
void ref_poly_add(poly *r, const poly *b);
void ref_poly_sub(poly *r, const poly *b);
void ref_poly_reduce(poly *r);

/* The candidates */
void mlkem_cbd2(int16_t r[256], const uint8_t buf[128]) WEAK;
void mlkem_cbd3(int16_t r[256], const uint8_t buf[192]) WEAK;
void mlkem_frommsg(int16_t r[256], const uint8_t msg[32]) WEAK;
void mlkem_frombytes(int16_t r[256], const uint8_t a[384]) WEAK;
uint64_t mlkem_check_encoding(const uint8_t *a, uint64_t k) WEAK;
void mlkem_add_reduce(int16_t r[256], const int16_t a[256]) WEAK;
uint64_t mlkem_rej_uniform_VARIABLE_TIME(int16_t r[256], const uint8_t *buf,
                                         uint64_t buflen,
                                         const uint8_t *table) WEAK;
uint64_t mlkem_rej_uniform_alt_VARIABLE_TIME(int16_t r[256], uint64_t n,
                                             const uint8_t *buf,
                                             uint64_t buflen,
                                             const uint8_t *table) WEAK;
extern const uint8_t ref_rej_uniform_table[4096] WEAK;
void mlkem_sub_reduce(int16_t r[256], const int16_t a[256]) WEAK;
void mlkem_tomsg(uint8_t msg[32], const int16_t a[256]) WEAK;
void mlkem_compress_d4(uint8_t r[128], const int16_t a[256]) WEAK;
void mlkem_compress_d5(uint8_t r[160], const int16_t a[256]) WEAK;
void mlkem_compress_d10(uint8_t r[320], const int16_t a[256]) WEAK;
void mlkem_compress_d11(uint8_t r[352], const int16_t a[256]) WEAK;
void mlkem_decompress_d4(int16_t r[256], const uint8_t a[128]) WEAK;
void mlkem_decompress_d5(int16_t r[256], const uint8_t a[160]) WEAK;
void mlkem_decompress_d10(int16_t r[256], const uint8_t a[320]) WEAK;
void mlkem_decompress_d11(int16_t r[256], const uint8_t a[352]) WEAK;

/* ------------------------------------------------------------------------- */

static uint64_t rng = 1;
static uint64_t rand64(void)
{
  uint64_t z = (rng += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}
static void randfill(void *p, size_t n)
{
  for (size_t i = 0; i < n; i++) ((uint8_t *)p)[i] = (uint8_t)rand64();
}

static unsigned long ntests = 10000, failures, checks;

#define GUARD 64
#define FILL 0xa5
/* An output area with guards; out() is where the function writes. */
typedef struct
{
  uint8_t b[GUARD + 4096 + GUARD];
} area;
static void *out(area *a)
{
  memset(a->b, FILL, sizeof(a->b));
  return a->b + GUARD;
}

/* Compare n bytes of candidate output with the reference, and check the
   guards around the candidate's n bytes. */
static int compare(const char *name, area *cand, const void *want, size_t n,
                   unsigned long test)
{
  const uint8_t *c = cand->b + GUARD;
  checks++;
  for (size_t i = 0; i < GUARD; i++)
    if (cand->b[i] != FILL || c[n + i] != FILL)
    {
      printf("FAIL %s test %lu: guard bytes overwritten\n", name, test);
      return 1;
    }
  for (size_t i = 0; i < n; i++)
    if (c[i] != ((const uint8_t *)want)[i])
    {
      printf("FAIL %s test %lu: byte %zu is 0x%02x, reference 0x%02x\n", name,
             test, i, c[i], ((const uint8_t *)want)[i]);
      return 1;
    }
  return 0;
}

static int same_input(const char *name, const void *p, const void *copy,
                      size_t n, unsigned long test)
{
  checks++;
  if (memcmp(p, copy, n) != 0)
  {
    printf("FAIL %s test %lu: input modified\n", name, test);
    return 1;
  }
  return 0;
}

/* ------------------------------------------------------------------------- */
/* CBD: bytes to coefficients. Tests 0..255 give every position every byte  */
/* value; the rest are random.                                              */
/* ------------------------------------------------------------------------- */

static void cbd_input(uint8_t *buf, size_t n, unsigned long t)
{
  if (t < 256)
    for (size_t i = 0; i < n; i++) buf[i] = (uint8_t)(t + 97 * i);
  else
    randfill(buf, n);
}

static int test_cbd2(void)
{
  uint8_t buf[128], copy[128];
  poly want;
  area a;
  for (unsigned long t = 0; t < 256 + ntests; t++)
  {
    cbd_input(buf, sizeof(buf), t);
    memcpy(copy, buf, sizeof(buf));
    ref_poly_cbd2(&want, buf);
    mlkem_cbd2(out(&a), buf);
    if (compare("mlkem_cbd2", &a, &want, 512, t) ||
        same_input("mlkem_cbd2", buf, copy, sizeof(buf), t))
      return 1;
  }
  return 0;
}

static int test_cbd3(void)
{
  uint8_t buf[192], copy[192];
  poly want;
  area a;
  for (unsigned long t = 0; t < 256 + ntests; t++)
  {
    cbd_input(buf, sizeof(buf), t);
    memcpy(copy, buf, sizeof(buf));
    ref_poly_cbd3(&want, buf);
    mlkem_cbd3(out(&a), buf);
    if (compare("mlkem_cbd3", &a, &want, 512, t) ||
        same_input("mlkem_cbd3", buf, copy, sizeof(buf), t))
      return 1;
  }
  return 0;
}

/* ------------------------------------------------------------------------- */
/* Compression: coefficients 0..q-1 to d-bit fields. Tests 0..q-1 give every */
/* position every value; the rest are random.                               */
/* ------------------------------------------------------------------------- */

static void canonical_input(poly *p, unsigned long t)
{
  for (int i = 0; i < 256; i++)
    p->coeffs[i] = (int16_t)(t < Q ? (t + 97 * (unsigned long)i) % Q
                                   : rand64() % Q);
}

static int test_compress(const char *name, unsigned d,
                         void (*cand)(uint8_t *, const int16_t *),
                         void (*ref)(uint8_t *, const poly *))
{
  uint8_t want[352];
  poly a, copy;
  area o;
  for (unsigned long t = 0; t < Q + ntests; t++)
  {
    canonical_input(&a, t);
    copy = a;
    ref(want, &a);
    cand(out(&o), a.coeffs);
    if (compare(name, &o, want, 32 * d, t) ||
        same_input(name, &a, &copy, sizeof(a), t))
      return 1;
  }
  return 0;
}

/* Decompression: d-bit fields to coefficients. Tests 0..2^d-1 give every */
/* field every value; the rest are random bytes.                         */

static void set_field(uint8_t *b, unsigned d, unsigned i, unsigned v)
{
  for (unsigned k = 0; k < d; k++)
  {
    unsigned bit = d * i + k;
    b[bit / 8] = (uint8_t)((b[bit / 8] & ~(1u << (bit % 8))) |
                           (((v >> k) & 1) << (bit % 8)));
  }
}

static int test_decompress(const char *name, unsigned d,
                           void (*cand)(int16_t *, const uint8_t *),
                           void (*ref)(poly *, const uint8_t *))
{
  uint8_t in[352], copy[352];
  poly want;
  area o;
  for (unsigned long t = 0; t < (1u << d) + ntests; t++)
  {
    if (t < (1u << d))
      for (unsigned i = 0; i < 256; i++)
        set_field(in, d, i, (unsigned)(t + 97 * i) & ((1u << d) - 1));
    else
      randfill(in, 32 * d);
    memcpy(copy, in, 32 * d);
    ref(&want, in);
    cand(out(&o), in);
    if (compare(name, &o, &want, 512, t) ||
        same_input(name, in, copy, 32 * d, t))
      return 1;
  }
  return 0;
}

#define COMPRESS_TEST(d)                                                  \
  static int test_compress_d##d(void)                                     \
  {                                                                       \
    return test_compress("mlkem_compress_d" #d, d, mlkem_compress_d##d,   \
                         ref_poly_compress_d##d);                         \
  }                                                                       \
  static int test_decompress_d##d(void)                                   \
  {                                                                       \
    return test_decompress("mlkem_decompress_d" #d, d,                    \
                           mlkem_decompress_d##d, ref_poly_decompress_d##d); \
  }
COMPRESS_TEST(4)
COMPRESS_TEST(5)
COMPRESS_TEST(10)
COMPRESS_TEST(11)

/* ------------------------------------------------------------------------- */
/* 12-bit encodings                                                          */
/* ------------------------------------------------------------------------- */

static int test_frombytes(void)
{
  uint8_t in[384], copy[384];
  poly want;
  area o;
  for (unsigned long t = 0; t < 4096 + ntests; t++)
  {
    if (t < 4096)
      for (unsigned i = 0; i < 256; i++)
        set_field(in, 12, i, (unsigned)(t + 97 * i) & 4095);
    else
      randfill(in, 384);
    memcpy(copy, in, 384);
    ref_poly_frombytes(&want, in);
    mlkem_frombytes(out(&o), in);
    if (compare("mlkem_frombytes", &o, &want, 512, t) ||
        same_input("mlkem_frombytes", in, copy, 384, t))
      return 1;
  }
  return 0;
}

/* The encoding check, against a direct model, for k = 0..4: valid
   encodings of random reduced coefficients, then one field changed to a
   value from q - 1 to 4095 (q - 1 and q among them each time), all
   fields 4095, and random bytes. */
static int test_check_encoding(void)
{
  static uint8_t in[4 * 384 + 64], copy[sizeof(in)];
  for (unsigned long t = 0; t < 4 * ntests + 64; t++)
  {
    uint64_t k = t % 5, want = 1, got;
    unsigned n = 256 * (unsigned)k, v;
    randfill(in, sizeof(in));
    for (unsigned i = 0; i < n; i++) set_field(in, 12, i, rand64() % Q);
    if (n && t % 4 != 0)
    {
      unsigned pos = (unsigned)(rand64() % n);
      v = t % 4 == 1   ? Q - 1
          : t % 4 == 2 ? Q
                       : Q + (unsigned)(rand64() % (4096 - Q));
      if (t % 64 == 3) v = 4095;
      set_field(in, 12, pos, v);
      want = v < Q;
    }
    if (n && t % 97 == 5)
    {
      randfill(in, 384 * k);
      want = 1;
      for (unsigned i = 0; i < n; i++)
      {
        unsigned b = 12 * i, f = (in[b / 8] | in[b / 8 + 1] << 8) >> (b % 8);
        if ((f & 4095) >= Q) want = 0;
      }
    }
    memcpy(copy, in, sizeof(in));
    got = mlkem_check_encoding(in, k);
    checks++;
    if (got != want)
    {
      printf("FAIL mlkem_check_encoding test %lu (k = %lu): %lu, want %lu\n",
             t, (unsigned long)k, (unsigned long)got, (unsigned long)want);
      return 1;
    }
    if (same_input("mlkem_check_encoding", in, copy, sizeof(in), t)) return 1;
  }
  return 0;
}

/* ------------------------------------------------------------------------- */
/* Add or subtract and reduce, for inputs whose sum or difference is less    */
/* than 2^15 in magnitude: random, extreme and boundary values.              */
/* ------------------------------------------------------------------------- */

static int16_t edge_value(unsigned long t, unsigned i)
{
  static const int16_t e[] = {0, 1, -1, 3328, -3328, 3329, -3329, 6658,
                              -6658, 16383, -16384, 16384, -16383, 32767 / 2,
                              -32767 / 2, 26632, -26632};
  unsigned n = sizeof(e) / sizeof(e[0]);
  return e[(t + i) % n];
}

static int test_addsub(int sub)
{
  const char *name = sub ? "mlkem_sub_reduce" : "mlkem_add_reduce";
  poly r, a, copy, want;
  area o;
  for (unsigned long t = 0; t < 20 + ntests; t++)
  {
    for (int i = 0; i < 256; i++)
    {
      int x, y, z;
      if (t < 20)
        x = edge_value(t, (unsigned)i), y = edge_value(t * 7 + 3, (unsigned)i);
      else if (t % 3 == 0)
        x = (int)(rand64() % 32768) - 16384,
        y = (int)(rand64() % 32768) - 16384;
      else
        x = (int)(rand64() % 65536) - 32768,
        y = (int)(rand64() % 65536) - 32768;
      z = sub ? x - y : x + y;
      if (z > 32767 || z < -32767) y = 0; /* keep within the precondition */
      r.coeffs[i] = (int16_t)x, a.coeffs[i] = (int16_t)y;
    }
    copy = a;
    want = r;
    if (sub)
      ref_poly_sub(&want, &a);
    else
      ref_poly_add(&want, &a);
    ref_poly_reduce(&want);
    memcpy(out(&o), &r, 512);
    (sub ? mlkem_sub_reduce : mlkem_add_reduce)((int16_t *)(o.b + GUARD),
                                                a.coeffs);
    if (compare(name, &o, &want, 512, t) ||
        same_input(name, &a, &copy, sizeof(a), t))
      return 1;
  }
  return 0;
}
static int test_add_reduce(void) { return test_addsub(0); }
static int test_sub_reduce(void) { return test_addsub(1); }

/* ------------------------------------------------------------------------- */
/* Rejection sampling: the alt version against the direct definition, on    */
/* random buffers with a varying proportion of rejected fields.              */
/* ------------------------------------------------------------------------- */

#include "mlkem_native2_consts.h"

static int test_rej_uniform_alt(void)
{
  static uint8_t buf[24 * 40], copy[sizeof(buf)];
  int16_t want[256];
  area o;
  for (unsigned long t = 0; t < 30 * 40 + ntests; t++)
  {
    uint64_t len = 24 * (t % 41), n, n0, got;
    unsigned bias = (unsigned)(t / 41) % 30; /* bytes forced to 0xff */
    int16_t *r;
    randfill(buf, sizeof(buf));
    for (size_t i = 0; i < sizeof(buf); i++)
      if (rand64() % 30 < bias) buf[i] = 0xff;
    memcpy(copy, buf, sizeof(buf));
    /* Start from n0 entries already present: 0 mostly, else random */
    n0 = t % 3 == 0 ? rand64() % 257 : 0;
    r = (int16_t *)out(&o);
    for (uint64_t i = 0; i < n0; i++) want[i] = r[i] = (int16_t)(rand64() % Q);
    n = n0;
    for (uint64_t i = 0; i + 3 <= len && n < 256; i += 3)
    {
      unsigned d1 = buf[i] | ((buf[i + 1] & 0xf) << 8);
      unsigned d2 = (buf[i + 1] >> 4) | (buf[i + 2] << 4);
      if (d1 < Q) want[n++] = (int16_t)d1;
      if (d2 < Q && n < 256) want[n++] = (int16_t)d2;
    }
    got = mlkem_rej_uniform_alt_VARIABLE_TIME(
        r, n0, buf, len, mlkem_native2_constants.rej_uniform_table);
    checks++;
    if (got != n)
    {
      printf("FAIL mlkem_rej_uniform_alt test %lu: count %lu, want %lu\n", t,
             (unsigned long)got, (unsigned long)n);
      return 1;
    }
    /* r[n..255] may be written too, but nothing beyond r */
    for (size_t i = 0; i < GUARD; i++)
      if (o.b[i] != FILL || o.b[GUARD + 512 + i] != FILL)
      {
        printf("FAIL mlkem_rej_uniform_alt test %lu: wrote outside r\n", t);
        return 1;
      }
    memset(o.b + GUARD + 2 * n, FILL, 512 - 2 * n);
    if (compare("mlkem_rej_uniform_alt", &o, want, 2 * n, t) ||
        same_input("mlkem_rej_uniform_alt", buf, copy, sizeof(buf), t))
      return 1;
  }
  return 0;
}

/* ------------------------------------------------------------------------- */
/* Messages                                                                  */
/* ------------------------------------------------------------------------- */

static int test_frommsg(void)
{
  uint8_t m[32], copy[32];
  poly want;
  area o;
  for (unsigned long t = 0; t < 256 + ntests; t++)
  {
    cbd_input(m, 32, t);
    memcpy(copy, m, 32);
    ref_poly_frommsg(&want, m);
    mlkem_frommsg(out(&o), m);
    if (compare("mlkem_frommsg", &o, &want, 512, t) ||
        same_input("mlkem_frommsg", m, copy, 32, t))
      return 1;
  }
  return 0;
}

static int test_tomsg(void)
{
  uint8_t want[32];
  poly a, copy;
  area o;
  for (unsigned long t = 0; t < Q + ntests; t++)
  {
    canonical_input(&a, t);
    copy = a;
    ref_poly_tomsg(want, &a);
    mlkem_tomsg(out(&o), a.coeffs);
    if (compare("mlkem_tomsg", &o, want, 32, t) ||
        same_input("mlkem_tomsg", &a, &copy, sizeof(a), t))
      return 1;
  }
  return 0;
}

/* ------------------------------------------------------------------------- */

typedef struct
{
  const char *name;
  void *fn;
  int (*test)(void);
} leaf;

#define LEAF(f) {#f, (void *)(f), test_##f}
#define LEAF2(f, t) {#f, (void *)(f), t}

int main(int argc, char **argv)
{
  const leaf leaves[] = {
      LEAF2(mlkem_cbd2, test_cbd2),
      LEAF2(mlkem_cbd3, test_cbd3),
      LEAF2(mlkem_frombytes, test_frombytes),
      LEAF2(mlkem_check_encoding, test_check_encoding),
      LEAF2(mlkem_rej_uniform_alt_VARIABLE_TIME, test_rej_uniform_alt),
      LEAF2(mlkem_add_reduce, test_add_reduce),
      LEAF2(mlkem_sub_reduce, test_sub_reduce),
      LEAF2(mlkem_frommsg, test_frommsg),
      LEAF2(mlkem_tomsg, test_tomsg),
      LEAF2(mlkem_compress_d4, test_compress_d4),
      LEAF2(mlkem_compress_d5, test_compress_d5),
      LEAF2(mlkem_compress_d10, test_compress_d10),
      LEAF2(mlkem_compress_d11, test_compress_d11),
      LEAF2(mlkem_decompress_d4, test_decompress_d4),
      LEAF2(mlkem_decompress_d5, test_decompress_d5),
      LEAF2(mlkem_decompress_d10, test_decompress_d10),
      LEAF2(mlkem_decompress_d11, test_decompress_d11),
  };
  const char *only = argc > 2 ? argv[2] : NULL;
  unsigned tested = 0, skipped = 0;
  if (argc > 1) ntests = strtoul(argv[1], NULL, 0);
  for (size_t i = 0; i < sizeof(leaves) / sizeof(leaves[0]); i++)
  {
    if (only && strcmp(only, leaves[i].name) != 0) continue;
    if (!leaves[i].fn)
    {
      skipped++;
      continue;
    }
    tested++;
    if (leaves[i].test())
      failures++;
    else
      printf("ok %s\n", leaves[i].name);
  }
  printf("%s: %u functions tested, %u not present, %lu checks, %lu "
         "failures\n",
         failures ? "FAIL" : "OK", tested, skipped, checks, failures);
  return failures != 0;
}
