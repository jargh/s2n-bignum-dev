#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Tests of the WireGuard part of wg_ref.py (common/wireguard.ml):
#
#  - X25519 (rfcx25519) against RFC 7748 Section 5.2 and the X25519 of the
#    "cryptography" package;
#  - complete handshakes between an initiator and a responder made of the
#    spec functions, which must agree on the state and the transport keys;
#  - the messages against a second, independent implementation of the
#    handshake built from hashlib, hmac and "cryptography" (written from
#    the WireGuard paper, not from wg_ref.py).
#
# Usage: python3 -I test_wg.py [SEED] [N]

import hashlib, hmac, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wg_ref as R
from cryptography.hazmat.primitives.asymmetric.x25519 import (
    X25519PrivateKey, X25519PublicKey)
from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
from cryptography.hazmat.primitives import serialization

failures = 0
def check(name, got, want):
    global failures
    if got != want:
        failures += 1
        print('FAIL', name)
        print('  got ', got.hex() if isinstance(got, bytes) else got)
        print('  want', want.hex() if isinstance(want, bytes) else want)

h = bytes.fromhex
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
count = int(sys.argv[2]) if len(sys.argv) > 2 else 20
rng = random.Random(seed)
rb = lambda n: bytes(rng.getrandbits(8) for _ in range(n))

# RFC 7748 5.2
check('x25519 rfc 1', R.wg_dh(
    h('a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4'),
    h('e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c')),
    h('c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552'))
# RFC 7748 6.1
alice = h('77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a')
bob = h('5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb')
check('x25519 alice', R.wg_dh_pubkey(alice),
      h('8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a'))
check('x25519 bob', R.wg_dh_pubkey(bob),
      h('de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f'))
check('x25519 shared', R.wg_dh(alice, R.wg_dh_pubkey(bob)),
      h('4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742'))

def lib_dh(priv, pub):
    return X25519PrivateKey.from_private_bytes(priv).exchange(
        X25519PublicKey.from_public_bytes(pub))

def lib_pub(priv):
    return X25519PrivateKey.from_private_bytes(priv).public_key().public_bytes(
        serialization.Encoding.Raw, serialization.PublicFormat.Raw)

for i in range(count):
    a, b = rb(32), rb(32)
    check('x25519 pub %d' % i, R.wg_dh_pubkey(a), lib_pub(a))
    try:
        want = lib_dh(a, b)
    except ValueError:          # all-zero result, rejected by the library
        want = bytes(32)
    check('x25519 dh %d' % i, R.wg_dh(a, b), want)

# An independent implementation of the handshake (Section 5.4 of the paper).

def HASH(x): return hashlib.blake2s(x).digest()
def HMAC(k, x): return hmac.new(k, x, hashlib.blake2s).digest()
def KDF(n, k, x):
    t0 = HMAC(k, x); out = []; t = b''
    for i in range(1, n + 1):
        t = HMAC(t0, t + bytes([i])); out.append(t)
    return out
def AEAD(k, ctr, p, a):
    return ChaCha20Poly1305(k).encrypt(bytes(4) + ctr.to_bytes(8, 'little'),
                                       p, a)
def DH(priv, pub): return lib_dh(priv, pub)
def PUB(priv): return lib_pub(priv)

def lib_initiation(si_priv, sr_pub, ei_priv, ts, sender):
    si_pub = PUB(si_priv)
    C = HASH(b'Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s')
    H = HASH(C + b'WireGuard v1 zx2c4 Jason@zx2c4.com')
    H = HASH(H + sr_pub)
    ei_pub = PUB(ei_priv)
    C, = KDF(1, C, ei_pub)
    H = HASH(H + ei_pub)
    C, k = KDF(2, C, DH(ei_priv, sr_pub))
    es = AEAD(k, 0, si_pub, H)
    H = HASH(H + es)
    C, k = KDF(2, C, DH(si_priv, sr_pub))
    et = AEAD(k, 0, ts, H)
    H = HASH(H + et)
    msg = bytes([1, 0, 0, 0]) + sender.to_bytes(4, 'little') + ei_pub + es + et
    return msg, C, H

def lib_response(C, H, ei_pub, si_pub, psk, er_priv, sender, receiver):
    er_pub = PUB(er_priv)
    C, = KDF(1, C, er_pub)
    H = HASH(H + er_pub)
    C, = KDF(1, C, DH(er_priv, ei_pub))
    C, = KDF(1, C, DH(er_priv, si_pub))
    C, tau, k = KDF(3, C, psk)
    H = HASH(H + tau)
    empty = AEAD(k, 0, b'', H)
    H = HASH(H + empty)
    msg = bytes([2, 0, 0, 0]) + sender.to_bytes(4, 'little') + \
          receiver.to_bytes(4, 'little') + er_pub + empty
    return msg, C, H

for i in range(count):
    si_priv, sr_priv = R.wg_clamp(rb(32)), R.wg_clamp(rb(32))
    si_pub, sr_pub = R.wg_dh_pubkey(si_priv), R.wg_dh_pubkey(sr_priv)
    psk = rb(32) if rng.random() < 0.5 else bytes(32)
    ei_priv, er_priv = R.wg_clamp(rb(32)), R.wg_clamp(rb(32))
    ts = R.wg_tai64n(rng.getrandbits(40), rng.randrange(10 ** 9))
    ii, ir = rng.getrandbits(32), rng.getrandbits(32)
    ss = R.wg_dh(si_priv, sr_pub)
    # initiator
    r1 = R.wg_create_initiation(si_pub, sr_pub, ss, ei_priv, ts, ii)
    msg1, ck_i, h_i = r1
    check('init vs lib %d' % i, r1,
          lib_initiation(si_priv, sr_pub, ei_priv, ts, ii))
    # responder
    e, s, ck, hh = R.wg_consume_initiation_static(sr_priv, sr_pub, msg1)
    check('static %d' % i, s, si_pub)
    check('ephemeral %d' % i, e, R.wg_dh_pubkey(ei_priv))
    t, ck_r, h_r = R.wg_consume_initiation_timestamp(
        R.wg_dh(sr_priv, s), (ck, hh), msg1)
    check('timestamp %d' % i, t, ts)
    check('state after initiation %d' % i, (ck_r, h_r), (ck_i, h_i))
    r2 = R.wg_create_response((ck_r, h_r), e, s, psk, er_priv, ir, ii)
    msg2, ck_r2, h_r2 = r2
    check('resp vs lib %d' % i, r2,
          lib_response(ck_r, h_r, e, s, psk, er_priv, ir, ii))
    # initiator again
    er, ck_i2, h_i2 = R.wg_consume_response((ck_i, h_i), ei_priv, si_priv,
                                            psk, msg2)
    check('state after response %d' % i, (ck_i2, h_i2), (ck_r2, h_r2))
    check('transport keys %d' % i, R.wg_transport_keys(ck_i2),
          R.wg_transport_keys(ck_r2))
    # tampering anywhere in the encrypted parts is rejected
    j = rng.randrange(40, 116)
    bad = msg1[:j] + bytes([msg1[j] ^ 1]) + msg1[j + 1:]
    r = R.wg_consume_initiation_static(sr_priv, sr_pub, bad)
    if r is not None:
        r = R.wg_consume_initiation_timestamp(R.wg_dh(sr_priv, r[1]),
                                              (r[2], r[3]), bad)
    check('tampered initiation %d' % i, r, None)
    j = rng.randrange(12, 60)
    bad = msg2[:j] + bytes([msg2[j] ^ 1]) + msg2[j + 1:]
    check('tampered response %d' % i,
          R.wg_consume_response((ck_i, h_i), ei_priv, si_priv, psk, bad), None)

print('%d failures' % failures)
sys.exit(1 if failures else 0)
