#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# A direct transcription into Python of the HOL Light specifications
# common/rfc7693.ml (BLAKE2s) and common/rfc8439.ml (ChaCha20, Poly1305,
# AEAD_CHACHA20_POLY1305, HChaCha20, XChaCha20-Poly1305), and later
# common/wireguard.ml, definition by definition, so that they can be tested
# against other implementations and against the kernel code. Byte strings
# are Python bytes; words are ints modulo 2^32. Only the standard library is
# used here.

M32 = 0xFFFFFFFF

def num_of_bytelist(b):
    return int.from_bytes(bytes(b), 'little')

def bytelist_of_num(k, n):
    return (n % (1 << (8 * k))).to_bytes(k, 'little')

def sub_list(i, n, l):
    return l[i:i + n]

def rol(x, n):
    return ((x << n) | (x >> (32 - n))) & M32

def ror(x, n):
    return ((x >> n) | (x << (32 - n))) & M32

# ---------------------------------------------------------------------------
# BLAKE2s (common/rfc7693.ml)
# ---------------------------------------------------------------------------

BLAKE2S_IV = [0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
              0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

BLAKE2S_SIGMA = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]

def blake2s_g(a, b, c, d, x, y, v):
    va = (v[a] + v[b] + x) & M32
    vd = ror(v[d] ^ va, 16)
    vc = (v[c] + vd) & M32
    vb = ror(v[b] ^ vc, 12)
    va2 = (va + vb + y) & M32
    vd2 = ror(vd ^ va2, 8)
    vc2 = (vc + vd2) & M32
    vb2 = ror(vb ^ vc2, 7)
    w = list(v)
    w[a], w[b], w[c], w[d] = va2, vb2, vc2, vd2
    return w

def blake2s_round(r, m, v):
    s = lambda j: m[BLAKE2S_SIGMA[r % 10][j]]
    v = blake2s_g(0, 4, 8, 12, s(0), s(1), v)
    v = blake2s_g(1, 5, 9, 13, s(2), s(3), v)
    v = blake2s_g(2, 6, 10, 14, s(4), s(5), v)
    v = blake2s_g(3, 7, 11, 15, s(6), s(7), v)
    v = blake2s_g(0, 5, 10, 15, s(8), s(9), v)
    v = blake2s_g(1, 6, 11, 12, s(10), s(11), v)
    v = blake2s_g(2, 7, 8, 13, s(12), s(13), v)
    v = blake2s_g(3, 4, 9, 14, s(14), s(15), v)
    return v

def blake2s_rounds(n, m, v):
    for r in range(n):
        v = blake2s_round(r, m, v)
    return v

def blake2s_compress(h, m, t, f):
    v0 = []
    for i in range(16):
        if i < 8: v0.append(h[i])
        elif i == 12: v0.append(BLAKE2S_IV[4] ^ (t & M32))
        elif i == 13: v0.append(BLAKE2S_IV[5] ^ ((t >> 32) & M32))
        elif i == 14 and f: v0.append(BLAKE2S_IV[6] ^ M32)
        else: v0.append(BLAKE2S_IV[i - 8])
    v = blake2s_rounds(10, m, v0)
    return [h[i] ^ v[i] ^ v[i + 8] for i in range(8)]

def blake2s_block(p, i):
    return [num_of_bytelist(sub_list(64 * i + 4 * j, 4, p)) for j in range(16)]

def blake2s_blocks(d, h, n):
    for i in range(n):
        h = blake2s_compress(h, d(i), 64 * (i + 1), False)
    return h

def blake2s_data(key, msg):
    d = (b'' if len(key) == 0 else key + bytes(64 - len(key))) + msg
    dd = max(1, (len(d) + 63) // 64)
    return dd, d + bytes(64 * dd - len(d))

def blake2s_bytes(h):
    return bytelist_of_num(32, sum(h[i] << (32 * i) for i in range(8)))

def blake2s(key, nn, msg):
    kk, ll = len(key), len(msg)
    dd, p = blake2s_data(key, msg)
    h0 = [BLAKE2S_IV[0] ^ 0x01010000 ^ ((kk << 8) & M32) ^ nn] + BLAKE2S_IV[1:]
    h = blake2s_blocks(lambda i: blake2s_block(p, i), h0, dd - 1)
    h2 = blake2s_compress(h, blake2s_block(p, dd - 1),
                          ll if kk == 0 else ll + 64, True)
    return sub_list(0, nn, blake2s_bytes(h2))

# ---------------------------------------------------------------------------
# ChaCha20, Poly1305 and the AEAD (common/rfc8439.ml)
# ---------------------------------------------------------------------------

def chacha20_qround(a, b, c, d, x):
    xa = (x[a] + x[b]) & M32
    xd = rol(x[d] ^ xa, 16)
    xc = (x[c] + xd) & M32
    xb = rol(x[b] ^ xc, 12)
    xa2 = (xa + xb) & M32
    xd2 = rol(xd ^ xa2, 8)
    xc2 = (xc + xd2) & M32
    xb2 = rol(xb ^ xc2, 7)
    w = list(x)
    w[a], w[b], w[c], w[d] = xa2, xb2, xc2, xd2
    return w

def chacha20_double_round(x):
    x = chacha20_qround(0, 4, 8, 12, x)
    x = chacha20_qround(1, 5, 9, 13, x)
    x = chacha20_qround(2, 6, 10, 14, x)
    x = chacha20_qround(3, 7, 11, 15, x)
    x = chacha20_qround(0, 5, 10, 15, x)
    x = chacha20_qround(1, 6, 11, 12, x)
    x = chacha20_qround(2, 7, 8, 13, x)
    x = chacha20_qround(3, 4, 9, 14, x)
    return x

def chacha20_rounds(n, x):
    for _ in range(n):
        x = chacha20_double_round(x)
    return x

def chacha20_le32(b, k):
    return num_of_bytelist(sub_list(4 * k, 4, b))

def chacha20_state(key, counter, nonce):
    x = []
    for i in range(16):
        if i == 0: x.append(0x61707865)
        elif i == 1: x.append(0x3320646e)
        elif i == 2: x.append(0x79622d32)
        elif i == 3: x.append(0x6b206574)
        elif i < 12: x.append(chacha20_le32(key, i - 4))
        elif i == 12: x.append(counter & M32)
        else: x.append(chacha20_le32(nonce, i - 13))
    return x

def chacha20_words(n, x):
    return bytelist_of_num(4 * n, sum(x[i] << (32 * i) for i in range(n)))

def chacha20_block(key, counter, nonce):
    x = chacha20_state(key, counter, nonce)
    y = chacha20_rounds(10, x)
    return chacha20_words(16, [(y[i] + x[i]) & M32 for i in range(16)])

def chacha20_encrypt(key, counter, nonce, m):
    return bytes(m[i] ^ chacha20_block(key, counter + i // 64, nonce)[i % 64]
                 for i in range(len(m)))

P1305 = (1 << 130) - 5

def poly1305_acc(r, msg, n):
    acc = 0
    for j in range(n):
        c = sub_list(16 * j, 16, msg)
        acc = ((acc + num_of_bytelist(c) + (1 << (8 * len(c)))) * r) % P1305
    return acc

def poly1305_r(key):
    return num_of_bytelist(sub_list(0, 16, key)) & \
           0x0ffffffc0ffffffc0ffffffc0fffffff

def poly1305(key, msg):
    return bytelist_of_num(16, poly1305_acc(poly1305_r(key), msg,
                                            (len(msg) + 15) // 16) +
                               num_of_bytelist(sub_list(16, 16, key)))

def poly1305_pad16(n):
    return bytes((16 - n % 16) % 16)

def aead_chacha20_poly1305_tag(key, nonce, aad, c):
    otk = sub_list(0, 32, chacha20_block(key, 0, nonce))
    return poly1305(otk, aad + poly1305_pad16(len(aad)) + c +
                         poly1305_pad16(len(c)) + bytelist_of_num(8, len(aad)) +
                         bytelist_of_num(8, len(c)))

def aead_chacha20_poly1305_encrypt(key, nonce, plain, aad):
    c = chacha20_encrypt(key, 1, nonce, plain)
    return c + aead_chacha20_poly1305_tag(key, nonce, aad, c)

def aead_chacha20_poly1305_decrypt(key, nonce, ct, aad):
    if len(ct) < 16:
        return None
    c = sub_list(0, len(ct) - 16, ct)
    if aead_chacha20_poly1305_tag(key, nonce, aad, c) == \
       sub_list(len(ct) - 16, 16, ct):
        return chacha20_encrypt(key, 1, nonce, c)
    return None

def hchacha20(key, nonce):
    x = chacha20_state(key, chacha20_le32(nonce, 0), sub_list(4, 12, nonce))
    y = chacha20_rounds(10, x)
    return chacha20_words(4, y) + chacha20_words(4, y[12:])

def xchacha20_nonce(nonce):
    return bytes(4) + sub_list(16, 8, nonce)

def xchacha20_poly1305_encrypt(key, nonce, plain, aad):
    return aead_chacha20_poly1305_encrypt(
        hchacha20(key, sub_list(0, 16, nonce)), xchacha20_nonce(nonce),
        plain, aad)

def xchacha20_poly1305_decrypt(key, nonce, ct, aad):
    return aead_chacha20_poly1305_decrypt(
        hchacha20(key, sub_list(0, 16, nonce)), xchacha20_nonce(nonce),
        ct, aad)

# ---------------------------------------------------------------------------
# X25519 as in HOL Light's EC/x25519.ml (rfcx25519 via purex25519 and the
# projective Montgomery ladder of EC/xzprojective.ml)
# ---------------------------------------------------------------------------

P25519 = 2 ** 255 - 19
A25519 = 486662

def montgomery_xzdouble(XZ):
    X, Z = XZ
    p = P25519
    return ((X * X - Z * Z) ** 2 % p,
            4 * (X * Z) * (X * X + A25519 * (X * Z) + Z * Z) % p)

def montgomery_xzdiffadd(XZ, XZm, XZn):
    (X, Z), (Xm, Zm), (Xn, Zn) = XZ, XZm, XZn
    p = P25519
    return (4 * Z * (Xm * Xn - Zm * Zn) ** 2 % p,
            4 * X * (Xm * Zn - Xn * Zm) ** 2 % p)

def x25519_ladderstep(b, P, P01):
    P0, P1 = P01
    if b:
        return (montgomery_xzdiffadd(P, P1, P0), montgomery_xzdouble(P1))
    return (montgomery_xzdouble(P0), montgomery_xzdiffadd(P, P1, P0))

def x25519_ladder(n, P):
    # if n = 0 then ((1,0),P) else ladderstep (n mod 2 = 1) P (ladder (n div 2) P)
    r = ((1, 0), P)
    for b in bin(n)[2:] if n > 0 else '':
        r = x25519_ladderstep(b == '1', P, r)
    return r

def purex25519(n, q):
    if q % P25519 == 0:
        return 0
    X, Z = x25519_ladder(n, (q, 1))[0]
    x, z = X % P25519, Z % P25519
    if z == 0:
        return 0
    return (x * pow(z, -1, P25519)) % P25519

def rfcx25519(n, q):
    return purex25519(2 ** 254 + (n % 2 ** 254 - n % 8), q % 2 ** 255)

# ---------------------------------------------------------------------------
# WireGuard (common/wireguard.ml)
# ---------------------------------------------------------------------------

WG_CONSTRUCTION = b'Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s'
WG_IDENTIFIER = b'WireGuard v1 zx2c4 Jason@zx2c4.com'
WG_LABEL_MAC1 = b'mac1----'
WG_LABEL_COOKIE = b'cookie--'

def wg_hash(x):
    return blake2s(b'', 32, x)

def wg_mac(key, x):
    return blake2s(key, 16, x)

def wg_hmac(key, x):
    k = wg_hash(key) if len(key) > 64 else key
    k0 = k + bytes(64 - len(k))
    return wg_hash(bytes(b ^ 0x5c for b in k0) +
                   wg_hash(bytes(b ^ 0x36 for b in k0) + x))

def wg_kdf_t(t0, n):
    t = b''
    for i in range(n):
        t = wg_hmac(t0, t + bytes([(i + 1) & 0xff]))
    return t

def wg_kdf1(key, x):
    return wg_kdf_t(wg_hmac(key, x), 1)

def wg_kdf2(key, x):
    t0 = wg_hmac(key, x)
    return wg_kdf_t(t0, 1), wg_kdf_t(t0, 2)

def wg_kdf3(key, x):
    t0 = wg_hmac(key, x)
    return wg_kdf_t(t0, 1), wg_kdf_t(t0, 2), wg_kdf_t(t0, 3)

def wg_dh(priv, pub):
    return bytelist_of_num(32, rfcx25519(num_of_bytelist(priv),
                                         num_of_bytelist(pub)))

def wg_dh_pubkey(priv):
    return wg_dh(priv, bytelist_of_num(32, 9))

WG_ZERO32 = bytes(32)

def wg_clamp(k):
    return bytes([k[0] & 248]) + k[1:31] + bytes([(k[31] & 127) | 64])

def wg_aead_nonce(counter):
    return bytes(4) + bytelist_of_num(8, counter)

def wg_aead(key, counter, plain, auth):
    return aead_chacha20_poly1305_encrypt(key, wg_aead_nonce(counter),
                                          plain, auth)

def wg_aead_decrypt(key, counter, ct, auth):
    return aead_chacha20_poly1305_decrypt(key, wg_aead_nonce(counter),
                                          ct, auth)

def wg_xaead(key, nonce, plain, auth):
    return xchacha20_poly1305_encrypt(key, nonce, plain, auth)

def wg_xaead_decrypt(key, nonce, ct, auth):
    return xchacha20_poly1305_decrypt(key, nonce, ct, auth)

M64 = (1 << 64) - 1

def wg_tai64n(sec, nsec):
    return (bytelist_of_num(8, (0x400000000000000a + sec) & M64)[::-1] +
            bytelist_of_num(4, (nsec & M64) & ~0xffffff & M64)[::-1])

WG_CK0 = wg_hash(WG_CONSTRUCTION)
WG_H0 = wg_hash(WG_CK0 + WG_IDENTIFIER)

def wg_mix_hash(h, x):
    return wg_hash(h + x)

def wg_handshake_init(spub):
    return WG_CK0, wg_mix_hash(WG_H0, spub)

def wg_ephemeral(ckh, e):
    ck, h = ckh
    return wg_kdf1(ck, e), wg_mix_hash(h, e)

def wg_encrypt(k, h, plain):
    c = wg_aead(k, 0, plain, h)
    return c, wg_mix_hash(h, c)

def wg_decrypt(k, h, c):
    p = wg_aead_decrypt(k, 0, c, h)
    return None if p is None else (p, wg_mix_hash(h, c))

def wg_le32(x):
    return bytelist_of_num(4, x)

def wg_initiation_msg(sender, e, es, et):
    return wg_le32(1) + wg_le32(sender) + e + es + et

def wg_response_msg(sender, receiver, e, empty):
    return wg_le32(2) + wg_le32(sender) + wg_le32(receiver) + e + empty

def wg_create_initiation(spub, rpub, ss, epriv, timestamp, sender):
    ck, h = wg_handshake_init(rpub)
    epub = wg_dh_pubkey(epriv)
    ck, h = wg_ephemeral((ck, h), epub)
    dh1 = wg_dh(epriv, rpub)
    ck, k = wg_kdf2(ck, dh1)
    es, h = wg_encrypt(k, h, spub)
    ck, k = wg_kdf2(ck, ss)
    et, h = wg_encrypt(k, h, timestamp)
    if WG_ZERO32 in (epriv, epub, dh1, ss):
        return None
    return wg_initiation_msg(sender, epub, es, et), ck, h

def wg_consume_initiation_static(spriv, spub, msg):
    e = sub_list(8, 32, msg)
    ck, h = wg_handshake_init(spub)
    ck, h = wg_ephemeral((ck, h), e)
    dh1 = wg_dh(spriv, e)
    ck, k = wg_kdf2(ck, dh1)
    if dh1 == WG_ZERO32:
        return None
    r = wg_decrypt(k, h, sub_list(40, 48, msg))
    if r is None:
        return None
    s, h = r
    return e, s, ck, h

def wg_consume_initiation_timestamp(ss, ckh, msg):
    ck, h = ckh
    ck, k = wg_kdf2(ck, ss)
    if ss == WG_ZERO32:
        return None
    r = wg_decrypt(k, h, sub_list(88, 28, msg))
    if r is None:
        return None
    t, h = r
    return t, ck, h

def wg_create_response(ckh, repub, rspub, psk, epriv, sender, receiver):
    ck, h = ckh
    epub = wg_dh_pubkey(epriv)
    ck, h = wg_ephemeral((ck, h), epub)
    dh1 = wg_dh(epriv, repub)
    ck = wg_kdf1(ck, dh1)
    dh2 = wg_dh(epriv, rspub)
    ck = wg_kdf1(ck, dh2)
    ck, tau, k = wg_kdf3(ck, psk)
    h = wg_mix_hash(h, tau)
    empty, h = wg_encrypt(k, h, b'')
    if WG_ZERO32 in (epriv, epub, dh1, dh2):
        return None
    return wg_response_msg(sender, receiver, epub, empty), ck, h

def wg_consume_response(ckh, epriv, spriv, psk, msg):
    ck, h = ckh
    e = sub_list(12, 32, msg)
    ck, h = wg_ephemeral((ck, h), e)
    dh1 = wg_dh(epriv, e)
    ck = wg_kdf1(ck, dh1)
    dh2 = wg_dh(spriv, e)
    ck = wg_kdf1(ck, dh2)
    ck, tau, k = wg_kdf3(ck, psk)
    h = wg_mix_hash(h, tau)
    if WG_ZERO32 in (dh1, dh2):
        return None
    r = wg_decrypt(k, h, sub_list(44, 16, msg))
    if r is None:
        return None
    return e, ck, r[1]

def wg_transport_keys(ck):
    return wg_kdf2(ck, b'')

def wg_mac1_key(rpub):
    return wg_hash(WG_LABEL_MAC1 + rpub)

def wg_mac1(rpub, msg):
    return wg_mac(wg_mac1_key(rpub), msg)

def wg_cookie_key(rpub):
    return wg_hash(WG_LABEL_COOKIE + rpub)
