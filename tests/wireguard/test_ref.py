#!/usr/bin/env python3
# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Tests of the Python transcription wg_ref.py of the HOL Light specs:
#
#  - test vectors of RFC 7693 and RFC 8439;
#  - random comparisons with Python's hashlib.blake2s and with the
#    ChaCha20 and ChaCha20Poly1305 of the "cryptography" package (OpenSSL);
#  - the ChaCha20-Poly1305 and XChaCha20-Poly1305 test vectors of the Linux
#    kernel (lib/crypto/chacha20poly1305-selftest.c, read as data), if the
#    path of that file is given as the first argument.
#
# Usage: python3 -I test_ref.py [chacha20poly1305-selftest.c] [SEED] [N]

import hashlib, os, random, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wg_ref as R

failures = 0
def check(name, got, want):
    global failures
    if got != want:
        failures += 1
        print('FAIL', name)
        print('  got ', got.hex() if isinstance(got, bytes) else got)
        print('  want', want.hex() if isinstance(want, bytes) else want)

h = bytes.fromhex
LADIES = (b"Ladies and Gentlemen of the class of '99: If I could offer you "
          b"only one tip for the future, sunscreen would be it.")

# RFC 7693 Appendix B: BLAKE2s-256("abc")
check('blake2s abc', R.blake2s(b'', 32, b'abc'),
      h('508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982'))

# RFC 8439 2.1.1, 2.3.2, 2.4.2, 2.5.2, 2.6.2, 2.8.2
x = [0] * 16
x[0], x[1], x[2], x[3] = 0x11111111, 0x01020304, 0x9b8d6f43, 0x01234567
y = R.chacha20_qround(0, 1, 2, 3, x)
check('qround', y[:4], [0xea2a92f4, 0xcb1cf8ce, 0x4581472e, 0x5881c4bb])
key = bytes(range(32))
check('block', R.chacha20_block(key, 1, h('000000090000004a00000000')),
      h('10f1e7e4d13b5915500fdd1fa32071c4c7d1f4c733c068030422aa9ac3d46c4e'
        'd2826446079faa0914c2d705d98b02a2b5129cd1de164eb9cbd083e8a2503c4e'))
check('encrypt', R.chacha20_encrypt(key, 1, h('000000000000004a00000000'),
                                    LADIES),
      h('6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0b'
        'f91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d8'
        '07ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab7793736'
        '5af90bbf74a35be6b40b8eedf2785e42874d'))
check('poly1305', R.poly1305(
        h('85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b'),
        b'Cryptographic Forum Research Group'),
      h('a8061dc1305136c6c22b8baf0c0127a9'))
key80 = bytes(range(0x80, 0xa0))
check('poly key gen', R.chacha20_block(key80, 0,
                                       h('000000000001020304050607'))[:32],
      h('8ad5a08b905f81cc815040274ab29471a833b637e3fd0da508dbb8e2fdd1a646'))
aad = h('50515253c0c1c2c3c4c5c6c7')
nonce = h('070000004041424344454647')
ct = R.aead_chacha20_poly1305_encrypt(key80, nonce, LADIES, aad)
check('aead', ct,
      h('d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6'
        '3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36'
        '92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc'
        '3ff4def08e4b7a9de576d26586cec64b6116'
        '1ae10b594f09e26a7e902ecbd0600691'))
check('aead decrypt', R.aead_chacha20_poly1305_decrypt(key80, nonce, ct, aad),
      LADIES)
bad = ct[:-1] + bytes([ct[-1] ^ 1])
check('aead reject', R.aead_chacha20_poly1305_decrypt(key80, nonce, bad, aad),
      None)

# draft-irtf-cfrg-xchacha-03 2.2.1: HChaCha20
check('hchacha20', R.hchacha20(key, h('000000090000004a0000000031415927')),
      h('82413b4227b27bfed30e42508a877d73a0f9e4d58a74a853c12ec41326d3ecdc'))

# Random comparisons with other implementations.
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
count = int(sys.argv[3]) if len(sys.argv) > 3 else 200
rng = random.Random(seed)
rb = lambda n: bytes(rng.getrandbits(8) for _ in range(n))

for i in range(count):
    kk = rng.choice([0, 0, 0, rng.randint(1, 32), 32])
    nn = rng.choice([32, 32, 16, rng.randint(1, 32)])
    ll = rng.choice([0, 1, 31, 32, 33, 63, 64, 65, 127, 128, 129,
                     rng.randint(0, 600)])
    k, m = rb(kk), rb(ll)
    check('blake2s random %d' % i, R.blake2s(k, nn, m),
          hashlib.blake2s(m, digest_size=nn, key=k).digest())

try:
    from cryptography.hazmat.primitives.ciphers.aead import ChaCha20Poly1305
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms
    have_crypto = True
except ImportError:
    have_crypto = False
    print('cryptography not available: skipping its comparisons')

if have_crypto:
    for i in range(count):
        k, n = rb(32), rb(12)
        p = rb(rng.choice([0, 1, 12, 15, 16, 17, 32, 63, 64, 65,
                           rng.randint(0, 400)]))
        a = rb(rng.choice([0, 1, 16, 32, rng.randint(0, 100)]))
        c = ChaCha20Poly1305(k).encrypt(n, p, a)
        check('aead random %d' % i, R.aead_chacha20_poly1305_encrypt(k, n, p, a), c)
        check('aead dec random %d' % i,
              R.aead_chacha20_poly1305_decrypt(k, n, c, a), p)
        if len(c) > 0:
            j = rng.randrange(len(c))
            t = c[:j] + bytes([c[j] ^ (1 << rng.randrange(8))]) + c[j + 1:]
            check('aead tamper %d' % i,
                  R.aead_chacha20_poly1305_decrypt(k, n, t, a), None)
        ctr = rng.getrandbits(32)
        enc = Cipher(algorithms.ChaCha20(k, ctr.to_bytes(4, 'little') + n),
                     mode=None).encryptor()
        # the counter wraps around within the stream only after 2^32 blocks
        if ctr + (len(p) + 63) // 64 < 2 ** 32:
            check('chacha20 random %d' % i,
                  R.chacha20_encrypt(k, ctr, n, p), enc.update(p))

# The kernel's own test vectors.
def kernel_vectors(path):
    text = open(path).read()
    arrays = {}
    for m in re.finditer(r'static const u8 (\w+)\[\] __initconst = \{([^}]*)\};',
                         text):
        arrays[m.group(1)] = bytes(int(v, 16) for v in
                                   re.findall(r'0x([0-9a-fA-F]{2})', m.group(2)))
    tables = {}
    for m in re.finditer(r'(\w+_vectors)\[\] __initconst = \{(.*?)\n\};',
                         text, re.S):
        vs = []
        for e in re.finditer(r'\{\s*(\w+),\s*(\w+),\s*(\w+),\s*(\w+),\s*(\w+),'
                             r'([^{}]*)\}', m.group(2)):
            rest = e.group(6)
            vs.append(tuple(arrays[e.group(j)] for j in range(1, 6)) +
                      ('true' in rest,))
        tables[m.group(1)] = vs
    return tables

def nonce12(n):
    return n if len(n) == 12 else bytes(4) + n

if len(sys.argv) > 1:
    t = kernel_vectors(sys.argv[1])
    for name in ('chacha20poly1305_enc_vectors', 'chacha20poly1305_dec_vectors',
                 'xchacha20poly1305_enc_vectors',
                 'xchacha20poly1305_dec_vectors'):
        print('%s: %d vectors' % (name, len(t[name])))
    for i, (inp, out, ad, n, k, fail) in \
            enumerate(t['chacha20poly1305_enc_vectors']):
        if len(n) in (8, 12):
            check('kernel enc %d' % i,
                  R.aead_chacha20_poly1305_encrypt(k, nonce12(n), inp, ad), out)
    for i, (inp, out, ad, n, k, fail) in \
            enumerate(t['chacha20poly1305_dec_vectors']):
        check('kernel dec %d' % i,
              R.aead_chacha20_poly1305_decrypt(k, nonce12(n), inp, ad),
              None if fail else out)
    for i, (inp, out, ad, n, k, fail) in \
            enumerate(t['xchacha20poly1305_enc_vectors']):
        check('kernel xenc %d' % i,
              R.xchacha20_poly1305_encrypt(k, n, inp, ad), out)
    for i, (inp, out, ad, n, k, fail) in \
            enumerate(t['xchacha20poly1305_dec_vectors']):
        check('kernel xdec %d' % i,
              R.xchacha20_poly1305_decrypt(k, n, inp, ad),
              None if fail else out)

print('%d failures' % failures)
sys.exit(1 if failures else 0)
