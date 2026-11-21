// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// ----------------------------------------------------------------------------
// A test harness that runs the code of the verified WireGuard image itself:
// it loads wireguard.so (as built by arm/wireguard/build.sh) with dlopen and
// provides the kernel functions that the image calls through its PLT, in a
// simple single-threaded form. The image's own peerlookup.c code keeps the
// index and public-key tables. The kernel structures are blocks of zeroed
// memory with the fields at the offsets of wg_offsets.h (gen_offsets.sh).
//
// Commands are read from stdin, one per line; results are printed to
// stdout as "name hex" lines. Devices and peers are numbered from 0.
//
//   rand HEX              queue bytes for get_random_bytes
//   index N               queue a value of get_random_u32 (the indices)
//   realtime SEC NSEC     the value of ktime_get_real_ts64
//   coarse NS             queue a value of ktime_get_coarse_with_offset
//   device PRIV           a device with that static private key
//   nodevice              a device without a static key
//   peer D PUB PSK        a peer of device D (PSK "-" for none)
//   create_init D P       wg_noise_handshake_create_initiation
//   consume_init D HEX    wg_noise_handshake_consume_initiation
//   create_resp D P       wg_noise_handshake_create_response
//   consume_resp D HEX    wg_noise_handshake_consume_response
//   begin D P             wg_noise_handshake_begin_session
//   show D P              the handshake state of a peer
//
// The kernel functions abort on anything a test does not expect.
// ----------------------------------------------------------------------------

#define _GNU_SOURCE
#include <dlfcn.h>
#include <signal.h>
#include <stdbool.h>
#include <ucontext.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "wg_offsets.h"

#define FIELD(p, off, type) (*(type *)((uint8_t *)(p) + (off)))
#define AT(p, off) ((uint8_t *)(p) + (off))

static void die(const char *msg)
{
  fprintf(stderr, "harness: %s\n", msg);
  exit(2);
}

// ----------------------------------------------------------------------------
// The kernel functions.
// ----------------------------------------------------------------------------

static uint8_t rnd[1 << 16];
static size_t rnd_len, rnd_pos;
static uint32_t idx_queue[256];
static int idx_len, idx_pos;
static int64_t real_sec, real_nsec;
static int64_t coarse_queue[256];
static int coarse_len, coarse_pos;

void down_read(void *sem) { (void)sem; }
void up_read(void *sem) { (void)sem; }
void down_write(void *sem) { (void)sem; }
void up_write(void *sem) { (void)sem; }
void __init_rwsem(void *sem, const char *name, void *key)
{ (void)sem; (void)name; (void)key; }

int wait_for_random_bytes(void) { return 0; }

static bool setup;               // fixed bytes while creating tables

void get_random_bytes(void *buf, size_t len)
{
  if (setup) { memset(buf, 0x5a, len); return; }
  if (rnd_pos + len > rnd_len) die("out of random bytes");
  memcpy(buf, rnd + rnd_pos, len);
  rnd_pos += len;
}

uint32_t get_random_u32(void)
{
  if (idx_pos >= idx_len) die("out of indices");
  return idx_queue[idx_pos++];
}

struct timespec64_k { int64_t tv_sec; long tv_nsec; };

void ktime_get_real_ts64(struct timespec64_k *ts)
{
  ts->tv_sec = real_sec;
  ts->tv_nsec = real_nsec;
}

int64_t ktime_get_coarse_with_offset(int offs)
{
  (void)offs;
  if (coarse_pos >= coarse_len) die("out of coarse times");
  return coarse_queue[coarse_pos++];
}

// Devices and peers.
#define MAXDEV 4
#define MAXPEER 16
static void *dev_tab[MAXDEV];
static int dev_n;
static void *peer_tab[MAXDEV][MAXPEER];
static int peer_n[MAXDEV];

void wg_peer_put(void *peer) { (void)peer; }
void *wg_peer_get_maybe_zero(void *peer) { return peer; }

void *__kmalloc_cache_noprof(void *cache, unsigned int flags, size_t size)
{
  (void)cache; (void)flags;
  return calloc(1, size);
}
void *__kvmalloc_node_noprof(size_t size, unsigned int flags, int node)
{
  (void)flags; (void)node;
  return calloc(1, size);
}
void mutex_lock(void *lock) { (void)lock; }
void mutex_unlock(void *lock) { (void)lock; }
void __mutex_init(void *lock, const char *name, void *key)
{ (void)lock; (void)name; (void)key; }
void kfree_sensitive(const void *p) { free((void *)p); }
void _raw_spin_lock_bh(void *lock) { (void)lock; }
void _raw_spin_unlock_bh(void *lock) { (void)lock; }
void __local_bh_enable_ip(unsigned long ip, unsigned int cnt)
{ (void)ip; (void)cnt; }
void call_rcu(void *head, void (*func)(void *)) { (void)head; (void)func; }
void refcount_warn_saturate(void *r, int t) { (void)r; (void)t;
  die("refcount_warn_saturate"); }

// Not used by the handshake functions that the tests call.
void wg_ratelimiter_allow(void) { die("wg_ratelimiter_allow"); }
void sg_miter_next(void) { die("sg_miter_next"); }
void sg_miter_stop(void) { die("sg_miter_stop"); }
void sg_miter_start(void) { die("sg_miter_start"); }
void sg_copy_buffer(void) { die("sg_copy_buffer"); }
void sg_nents(void) { die("sg_nents"); }

// ----------------------------------------------------------------------------
// The image.
// ----------------------------------------------------------------------------

static void (*noise_init)(void);
static void (*set_private_key)(void *, const uint8_t *);
static void (*handshake_init)(void *, void *, const uint8_t *, const uint8_t *,
                              void *);
static bool (*create_init)(void *, void *);
static void *(*consume_init)(void *, void *);
static bool (*create_resp)(void *, void *);
static void *(*consume_resp)(void *, void *);
static bool (*begin_session)(void *, void *);
static void *(*pubkey_alloc)(void);
static void (*pubkey_add)(void *, void *);
static void *(*index_alloc)(void);

static void *sym(void *h, const char *name)
{
  void *p = dlsym(h, name);
  if (!p) { fprintf(stderr, "harness: no symbol %s\n", name); exit(2); }
  return p;
}

static void load_image(const char *path)
{
  void *h = dlopen(path, RTLD_NOW | RTLD_GLOBAL);
  if (!h) { fprintf(stderr, "harness: %s\n", dlerror()); exit(2); }
  // __va(__pa_symbol(empty_zero_page)) is empty_zero_page itself with these
  // values: the linear map coincides with the image.
  *(uint64_t *)sym(h, "kimage_voffset") = 0;
  *(uint64_t *)sym(h, "memstart_addr") = 0xfff0000000000000ULL;
  noise_init = sym(h, "wg_noise_init");
  set_private_key = sym(h, "wg_noise_set_static_identity_private_key");
  handshake_init = sym(h, "wg_noise_handshake_init");
  create_init = sym(h, "wg_noise_handshake_create_initiation");
  consume_init = sym(h, "wg_noise_handshake_consume_initiation");
  create_resp = sym(h, "wg_noise_handshake_create_response");
  consume_resp = sym(h, "wg_noise_handshake_consume_response");
  begin_session = sym(h, "wg_noise_handshake_begin_session");
  pubkey_alloc = sym(h, "wg_pubkey_hashtable_alloc");
  pubkey_add = sym(h, "wg_pubkey_hashtable_add");
  index_alloc = sym(h, "wg_index_hashtable_alloc");
  noise_init();
}

// ----------------------------------------------------------------------------
// Commands.
// ----------------------------------------------------------------------------

static int hexval(int c)
{
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  die("bad hex");
  return 0;
}

static size_t unhex(const char *s, uint8_t *out, size_t max)
{
  size_t n = strlen(s);
  if (n % 2 || n / 2 > max) die("bad hex length");
  for (size_t i = 0; i < n / 2; i++)
    out[i] = (uint8_t)(hexval(s[2 * i]) * 16 + hexval(s[2 * i + 1]));
  return n / 2;
}

static void puthex(const char *name, const void *p, size_t n)
{
  printf("%s ", name);
  for (size_t i = 0; i < n; i++) printf("%02x", ((const uint8_t *)p)[i]);
  printf("\n");
}

static void *getpeer(int d, int p)
{
  if (d < 0 || d >= dev_n || p < 0 || p >= peer_n[d]) die("bad peer");
  return peer_tab[d][p];
}

static void show(int d, int p)
{
  uint8_t *hs = AT(getpeer(d, p), WG_wg_peer_handshake);
  printf("state %d\n", FIELD(hs, WG_noise_handshake_state, int));
  puthex("hash", hs + WG_noise_handshake_hash, 32);
  puthex("chaining_key", hs + WG_noise_handshake_chaining_key, 32);
  puthex("ephemeral_private", hs + WG_noise_handshake_ephemeral_private, 32);
  puthex("remote_ephemeral", hs + WG_noise_handshake_remote_ephemeral, 32);
  puthex("latest_timestamp", hs + WG_noise_handshake_latest_timestamp, 12);
  puthex("remote_index", hs + WG_noise_handshake_remote_index, 4);
  printf("last_initiation_consumption %lld\n", (long long)
         FIELD(hs, WG_noise_handshake_last_initiation_consumption, int64_t));
}

static int peer_number(void *peer)
{
  for (int d = 0; d < dev_n; d++)
    for (int p = 0; p < peer_n[d]; p++)
      if (peer_tab[d][p] == peer) return p;
  return -1;
}

static void *new_device(void)
{
  if (dev_n >= MAXDEV) die("too many devices");
  void *dev = calloc(1, WG_wg_device_size);
  setup = true;
  FIELD(dev, WG_wg_device_peer_hashtable, void *) = pubkey_alloc();
  FIELD(dev, WG_wg_device_index_hashtable, void *) = index_alloc();
  setup = false;
  dev_tab[dev_n++] = dev;
  return dev;
}

// The kernel code reads the current task as MRS Xt, SP_EL0 (for the RCU
// read-side sections of wg_noise_handshake_begin_session), which traps at
// EL0: emulate it with a zeroed task structure.

static uint8_t fake_task[1 << 14] __attribute__((aligned(64)));

static void sigill(int sig, siginfo_t *si, void *uc_)
{
  (void)sig; (void)si;
  ucontext_t *uc = uc_;
  uint32_t insn = *(uint32_t *)uc->uc_mcontext.pc;
  if ((insn & 0xffffffe0u) != 0xd5384100u) die("illegal instruction");
  unsigned rt = insn & 31;
  if (rt != 31) uc->uc_mcontext.regs[rt] = (uint64_t)(uintptr_t)fake_task;
  uc->uc_mcontext.pc += 4;
}

int main(int argc, char **argv)
{
  if (argc != 2) die("usage: wg_harness wireguard.so < commands");
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_sigaction = sigill;
  sa.sa_flags = SA_SIGINFO;
  sigaction(SIGILL, &sa, NULL);
  load_image(argv[1]);
  setvbuf(stdout, NULL, _IOLBF, 0);
  static char line[1 << 17];
  static uint8_t buf[1 << 16];
  while (fgets(line, sizeof line, stdin)) {
    static char cmd[32], a1[1 << 16], a2[1 << 12], a3[256];
    a1[0] = a2[0] = a3[0] = 0;
    line[strcspn(line, "\n")] = 0;
    if (sscanf(line, "%31s %65535s %4095s %255s", cmd, a1, a2, a3) < 1)
      continue;
    if (!strcmp(cmd, "rand")) {
      rnd_len += unhex(a1, rnd + rnd_len, sizeof rnd - rnd_len);
    } else if (!strcmp(cmd, "index")) {
      idx_queue[idx_len++] = (uint32_t)strtoul(a1, NULL, 0);
    } else if (!strcmp(cmd, "realtime")) {
      real_sec = strtoll(a1, NULL, 0);
      real_nsec = strtoll(a2, NULL, 0);
    } else if (!strcmp(cmd, "coarse")) {
      coarse_queue[coarse_len++] = strtoll(a1, NULL, 0);
    } else if (!strcmp(cmd, "device") || !strcmp(cmd, "nodevice")) {
      void *dev = new_device();
      if (!strcmp(cmd, "device")) {
        if (unhex(a1, buf, 32) != 32) die("bad key");
        set_private_key(AT(dev, WG_wg_device_static_identity), buf);
      }
      printf("has_identity %d\n", FIELD(dev, WG_wg_device_static_identity +
             WG_noise_static_identity_has_identity, uint8_t));
      puthex("static_public", AT(dev, WG_wg_device_static_identity +
             WG_noise_static_identity_static_public), 32);
    } else if (!strcmp(cmd, "peer")) {
      int d = atoi(a1);
      uint8_t pub[32], psk[32];
      if (d < 0 || d >= dev_n || peer_n[d] >= MAXPEER) die("bad device");
      if (unhex(a2, pub, 32) != 32) die("bad key");
      bool havepsk = strcmp(a3, "-");
      if (havepsk && unhex(a3, psk, 32) != 32) die("bad psk");
      void *dev = dev_tab[d];
      void *peer = calloc(1, WG_wg_peer_size);
      FIELD(peer, WG_wg_peer_device, void *) = dev;
      peer_tab[d][peer_n[d]++] = peer;
      handshake_init(AT(peer, WG_wg_peer_handshake),
                     AT(dev, WG_wg_device_static_identity), pub,
                     havepsk ? psk : NULL, peer);
      pubkey_add(FIELD(dev, WG_wg_device_peer_hashtable, void *), peer);
      puthex("precomputed_static_static", AT(peer, WG_wg_peer_handshake +
             WG_noise_handshake_precomputed_static_static), 32);
    } else if (!strcmp(cmd, "create_init")) {
      int d = atoi(a1), p = atoi(a2);
      uint8_t msg[WG_message_handshake_initiation_size];
      memset(msg, 0xee, sizeof msg);
      bool r = create_init(msg, AT(getpeer(d, p), WG_wg_peer_handshake));
      printf("ret %d\n", r);
      puthex("msg", msg, sizeof msg);
      show(d, p);
    } else if (!strcmp(cmd, "consume_init")) {
      int d = atoi(a1);
      uint8_t msg[WG_message_handshake_initiation_size];
      if (unhex(a2, msg, sizeof msg) != sizeof msg) die("bad message");
      void *peer = consume_init(msg, dev_tab[d]);
      int p = peer ? peer_number(peer) : -1;
      printf("peer %d\n", p);
      if (p >= 0) show(d, p);
    } else if (!strcmp(cmd, "create_resp")) {
      int d = atoi(a1), p = atoi(a2);
      uint8_t msg[WG_message_handshake_response_size];
      memset(msg, 0xee, sizeof msg);
      bool r = create_resp(msg, AT(getpeer(d, p), WG_wg_peer_handshake));
      printf("ret %d\n", r);
      puthex("msg", msg, sizeof msg);
      show(d, p);
    } else if (!strcmp(cmd, "consume_resp")) {
      int d = atoi(a1);
      uint8_t msg[WG_message_handshake_response_size];
      if (unhex(a2, msg, sizeof msg) != sizeof msg) die("bad message");
      void *peer = consume_resp(msg, dev_tab[d]);
      int p = peer ? peer_number(peer) : -1;
      printf("peer %d\n", p);
      if (p >= 0) show(d, p);
    } else if (!strcmp(cmd, "begin")) {
      int d = atoi(a1), p = atoi(a2);
      void *peer = getpeer(d, p);
      bool r = begin_session(AT(peer, WG_wg_peer_handshake),
                             AT(peer, WG_wg_peer_keypairs));
      printf("ret %d\n", r);
      void *kp = FIELD(peer, WG_wg_peer_keypairs +
                       WG_noise_keypairs_next_keypair, void *);
      if (!kp) kp = FIELD(peer, WG_wg_peer_keypairs +
                          WG_noise_keypairs_current_keypair, void *);
      if (kp) {
        puthex("sending", AT(kp, WG_noise_keypair_sending +
                             WG_noise_symmetric_key_key), 32);
        puthex("receiving", AT(kp, WG_noise_keypair_receiving +
                               WG_noise_symmetric_key_key), 32);
        printf("initiator %d\n",
               FIELD(kp, WG_noise_keypair_i_am_the_initiator, uint8_t));
      }
      show(d, p);
    } else if (!strcmp(cmd, "show")) {
      show(atoi(a1), atoi(a2));
    } else {
      die("unknown command");
    }
  }
  return 0;
}
