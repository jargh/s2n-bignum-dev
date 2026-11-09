/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 */

/*
 * Cycles per call of the ML-KEM API functions (all three parameter sets),
 * for the library this is linked with. There are no PMU or perf counters
 * on this host, so time is read from cntvct_el0 (1 GHz here) and turned
 * into cycles with the clock frequency measured by a chain of dependent
 * additions. Each figure is the median over NTESTS runs of NITER calls,
 * after NWARMUP calls.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NTESTS 31
#define NITER 200
#define NWARMUP 50

static inline uint64_t ticks(void)
{
  uint64_t t;
  __asm__ volatile("isb; mrs %0, cntvct_el0" : "=r"(t));
  return t;
}

static uint64_t tick_hz(void)
{
  uint64_t f;
  __asm__ volatile("mrs %0, cntfrq_el0" : "=r"(f));
  return f;
}

/* Clock frequency in cycles per tick: 1000 dependent additions per
   iteration, the fastest of 20 runs. */
static double cycles_per_tick(void)
{
  uint64_t best = ~(uint64_t)0;
  for (int r = 0; r < 20; r++)
  {
    uint64_t x = 1, t0 = ticks();
    for (int i = 0; i < 10000; i++)
      __asm__ volatile(".rept 1000\n add %0, %0, %0\n .endr" : "+r"(x));
    uint64_t t = ticks() - t0;
    if (t < best) best = t;
  }
  return 1e7 / (double)best;
}

static int cmp_u64(const void *a, const void *b)
{
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return (x > y) - (x < y);
}

static double cpt;

#define BENCH(name, call)                                          \
  do                                                               \
  {                                                                \
    uint64_t t[NTESTS];                                            \
    for (int w = 0; w < NWARMUP; w++) (void)(call);                \
    for (int k = 0; k < NTESTS; k++)                               \
    {                                                              \
      uint64_t t0 = ticks();                                       \
      for (int i = 0; i < NITER; i++) (void)(call);                \
      t[k] = ticks() - t0;                                         \
    }                                                              \
    qsort(t, NTESTS, sizeof(uint64_t), cmp_u64);                   \
    printf("%-26s %9.0f\n", name,                                  \
           (double)t[NTESTS / 2] * cpt / (double)NITER);           \
  } while (0)

/* Deterministic randombytes for the randomized API functions. */
static uint64_t rng_state = 0x0123456789abcdefULL;
int randombytes(uint8_t *out, size_t outlen)
{
  for (size_t i = 0; i < outlen; i++)
  {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    out[i] = (uint8_t)rng_state;
  }
  return 0;
}

#define DECLARE(L)                                                        \
  int mlkem##L##_keypair_derand(uint8_t *, uint8_t *, const uint8_t *);   \
  int mlkem##L##_keypair(uint8_t *, uint8_t *) __attribute__((weak));     \
  int mlkem##L##_enc_derand(uint8_t *, uint8_t *, const uint8_t *,        \
                            const uint8_t *);                             \
  int mlkem##L##_enc(uint8_t *, uint8_t *, const uint8_t *)               \
      __attribute__((weak));                                              \
  int mlkem##L##_dec(uint8_t *, const uint8_t *, const uint8_t *);        \
  int mlkem##L##_check_pk(const uint8_t *);                               \
  int mlkem##L##_check_sk(const uint8_t *);
DECLARE(512)
DECLARE(768)
DECLARE(1024)

#define RUN(L)                                                            \
  do                                                                      \
  {                                                                       \
    static uint8_t pk[1568], sk[3168], ct[1568], ss[32], coins[64];      \
    randombytes(coins, 64);                                               \
    mlkem##L##_keypair_derand(pk, sk, coins);                             \
    mlkem##L##_enc_derand(ct, ss, pk, coins);                             \
    BENCH("mlkem" #L "_keypair_derand",                                   \
          mlkem##L##_keypair_derand(pk, sk, coins));                      \
    if (mlkem##L##_keypair)                                               \
      BENCH("mlkem" #L "_keypair", mlkem##L##_keypair(pk, sk));           \
    BENCH("mlkem" #L "_enc_derand",                                       \
          mlkem##L##_enc_derand(ct, ss, pk, coins));                      \
    if (mlkem##L##_enc)                                                   \
      BENCH("mlkem" #L "_enc", mlkem##L##_enc(ct, ss, pk));               \
    BENCH("mlkem" #L "_dec", mlkem##L##_dec(ss, ct, sk));                 \
    BENCH("mlkem" #L "_check_pk", mlkem##L##_check_pk(pk));               \
    BENCH("mlkem" #L "_check_sk", mlkem##L##_check_sk(sk));               \
  } while (0)

int main(int argc, char **argv)
{
  cpt = cycles_per_tick();
  printf("# clock %.3f GHz (timer %.3f GHz)%s%s\n",
         cpt * (double)tick_hz() / 1e9, (double)tick_hz() / 1e9,
         argc > 1 ? ", " : "", argc > 1 ? argv[1] : "");
  RUN(512);
  RUN(768);
  RUN(1024);
  return 0;
}
