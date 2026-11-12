# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Compare a build of puff with the spec mirror: on streams from zlib, at
# all levels and strategies, on mutations of them, on crafted streams as in
# craft.py and on random bytes, with output buffers of various sizes. The
# return code must be 0 with the expected output and lengths if the mirror
# accepts the stream and the output fits, 1 if it does not fit, and nonzero
# if the mirror rejects the stream. PUFF_RUN is a program built from
# puff_run.c, e.g. the AArch64 one from ../../arm/puff/build_puff.sh (run
# under qemu-user on other machines).
# usage: python3 -I diff_puff.py PUFF_RUN SEED N
import os, random, subprocess, sys, tempfile, zlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rfc1951_ref as ref
import craft

puff_run, seed, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
craft.rng.seed(seed)


def fnv(b):
    h = 1469598103934665603
    for x in b:
        h = ((h ^ x) * 1099511628211) % 2 ** 64
    return '%016x' % h


def zstream():
    n = rng.choice([0, 1, 10, 100, 1000, 20000])
    kind = rng.randrange(3)
    if kind == 0:
        data = bytes(rng.randrange(256) for _ in range(n))
    elif kind == 1:
        data = bytes(rng.choice(b'abcd ') for _ in range(n))
    else:
        data = bytes([rng.randrange(256)]) * n
    c = zlib.compressobj(rng.randrange(10), zlib.DEFLATED, -15,
                         rng.randrange(1, 10),
                         rng.choice([zlib.Z_DEFAULT_STRATEGY, zlib.Z_FIXED,
                                     zlib.Z_HUFFMAN_ONLY, zlib.Z_RLE]))
    return c.compress(data) + c.flush()


def mutate(s):
    s = bytearray(s)
    if s and rng.randrange(2):
        s[rng.randrange(len(s))] ^= 1 << rng.randrange(8)
    if s and rng.randrange(3) == 0:
        del s[rng.randrange(len(s)):]
    return bytes(s)


cases = []
for i in range(N):
    r = rng.randrange(4)
    s = zstream() if r == 0 else mutate(zstream()) if r == 1 else \
        craft.stream() if r == 2 else \
        bytes(rng.randrange(256) for _ in range(rng.randrange(1, 30)))
    cases.append(s)

tmp = tempfile.mkdtemp(prefix='puffdiff')
lines, expect = [], []
for i, s in enumerate(cases):
    p = os.path.join(tmp, '%d.bin' % i)
    open(p, 'wb').write(s)
    r = ref.decode(s)
    if r is None:
        size = rng.choice([0, 100, 70000])
    else:
        out = r[0]
        size = rng.choice([len(out), len(out) + 5, max(0, len(out) - 1)])
    lines.append('%s %d' % (p, size))
    expect.append((r, size))

res = subprocess.run([puff_run], input='\n'.join(lines) + '\n',
                     capture_output=True, text=True).stdout.split('\n')
bad = 0
counts = {}
for (r, size), line in zip(expect, res):
    _, rc, destlen, sourcelen, h = line.split()
    rc, destlen, sourcelen = int(rc), int(destlen), int(sourcelen)
    counts[rc] = counts.get(rc, 0) + 1
    if r is not None and len(r[0]) <= size:
        ok = rc == 0 and destlen == len(r[0]) and sourcelen == r[1] and \
            h == fnv(r[0])
    elif r is not None:
        ok = rc == 1
    else:
        ok = rc != 0
    if not ok:
        bad += 1
        if bad <= 5:
            print('MISMATCH', line, r and (len(r[0]), r[1]), size)
print('return codes:', sorted(counts.items()))
print('cases', len(cases), 'MISMATCHES', bad)
