# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Differential tests of rfc1951_ref.decode against zlib's raw inflate.
# usage: python3 -I test_ref.py [SEED] [N]
import os, random, sys, zlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rfc1951_ref as ref

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
N = int(sys.argv[2]) if len(sys.argv) > 2 else 300
rng = random.Random(seed)


def zlib_decode(data):
    """(output, bytes used) if zlib finds a complete raw stream, else None."""
    d = zlib.decompressobj(-15)
    try:
        out = d.decompress(data)
    except zlib.error:
        return None
    if not d.eof:
        return None
    return out, len(data) - len(d.unused_data)


def sample_text(n):
    words = [rng.choice(['the', 'deflate', 'format', 'is', 'a', 'stream',
                         'of', 'blocks', 'huffman', 'code', 'length', 'x'])
             for _ in range(n)]
    return ' '.join(words).encode()[:n]


def sample_data(n):
    kind = rng.randrange(5)
    if kind == 0:
        return bytes(rng.randrange(256) for _ in range(n))
    if kind == 1:
        return sample_text(n)
    if kind == 2:
        return bytes(rng.choice(b'ab') for _ in range(n))
    if kind == 3:
        return bytes([rng.randrange(256)]) * n
    return bytes(rng.randrange(4) for _ in range(n))


def compress(data):
    level = rng.randrange(10)
    strategy = rng.choice([zlib.Z_DEFAULT_STRATEGY, zlib.Z_FILTERED,
                           zlib.Z_HUFFMAN_ONLY, zlib.Z_RLE, zlib.Z_FIXED])
    c = zlib.compressobj(level, zlib.DEFLATED, -15, rng.randrange(1, 10),
                         strategy)
    out = b''
    pos = 0
    while pos < len(data):
        k = rng.randrange(1, max(2, len(data) // 3 + 1))
        out += c.compress(data[pos:pos + k])
        pos += k
        if rng.randrange(4) == 0:
            out += c.flush(rng.choice([zlib.Z_SYNC_FLUSH, zlib.Z_FULL_FLUSH,
                                       zlib.Z_PARTIAL_FLUSH]))
    return out + c.flush(zlib.Z_FINISH)


def mutate(data):
    data = bytearray(data)
    for _ in range(rng.randrange(1, 4)):
        kind = rng.randrange(4)
        if kind == 0 and data:
            i = rng.randrange(len(data))
            data[i] ^= 1 << rng.randrange(8)
        elif kind == 1 and data:
            del data[rng.randrange(len(data)):]
        elif kind == 2:
            data += bytes(rng.randrange(256) for _ in range(rng.randrange(4)))
        elif data:
            data[rng.randrange(len(data))] = rng.randrange(256)
    return bytes(data)


stats = {'valid': 0, 'mutated_ok': 0, 'mutated_bad': 0, 'random_ok': 0,
         'random_bad': 0}
mismatches = []
for t in range(N):
    data = sample_data(rng.choice([0, 1, 2, 10, 100, 1000, 5000, 40000]))
    comp = compress(data)
    trail = bytes(rng.randrange(256) for _ in range(rng.randrange(3)))
    r = ref.decode(comp + trail)
    if r != (data, len(comp)):
        mismatches.append(('valid', comp + trail, r and len(r[0])))
    else:
        stats['valid'] += 1
    for _ in range(5):
        m = mutate(comp)
        a, b = ref.decode(m), zlib_decode(m)
        if a != b:
            mismatches.append(('mutated', m, (a and len(a[0]), b and
                                              len(b[0]))))
        else:
            stats['mutated_ok' if a else 'mutated_bad'] += 1
    m = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 40)))
    a, b = ref.decode(m), zlib_decode(m)
    if a != b:
        mismatches.append(('random', m, (a and len(a[0]), b and len(b[0]))))
    else:
        stats['random_ok' if a else 'random_bad'] += 1
print(stats)
print('MISMATCHES', len(mismatches))
for kind, m, info in mismatches[:10]:
    print(kind, m[:40].hex(), info)
