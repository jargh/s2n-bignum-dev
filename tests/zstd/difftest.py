# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Differential tests of the mirror rfc8878_ref.py against zstd, through the
# test program zhuf_run (zhuf_run.c, built by ../../arm/zstd/build_zstd.sh
# with zstd's decoding in the AArch64 library, or natively). The inputs are
# made from N inputs of each kind: Huffman-coded literals from zstd's
# encoder and mutations of them, raw and FSE-compressed tree descriptions
# with random and crafted weights, crafted prefix codes up to 12 bits deep,
# FSE table descriptions with long runs of zeros and running past the end
# of their input, and the example of RFC 8878 section 4.2.2. zstd must agree
# exactly with the zstd reading of the mirror, and with the RFC reading
# except for the reasons in the list allowed below.
# usage: python3 -I -B difftest.py ZHUF_RUN SEED N
import random, subprocess, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rfc8878_ref as ref

run, seed, N = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)


def drive(lines):
    p = subprocess.run([run], input='\n'.join(lines) + '\n',
                       capture_output=True, text=True)
    out = p.stdout.splitlines()
    assert len(out) == len(lines), (len(out), len(lines), p.stderr[:500])
    return out


# ---- an NCount writer (the inverse of the reader), for crafted inputs ----

def ncount_bits(counts, al):
    bits = []
    def put(v, n):
        bits.extend((v >> i) & 1 for i in range(n))
    put(al - 5, 4)
    remaining = 1 << al
    i = 0
    while i < len(counts) and remaining > 0:
        c = counts[i]
        v = c + 1
        top = remaining + 1
        nb = top.bit_length()
        small = (1 << nb) - 1 - top
        if v < small:
            put(v, nb - 1)
        elif v < (1 << (nb - 1)):
            put(v, nb)
        else:
            put(v + small, nb)
        remaining -= 1 if c == -1 else c
        i += 1
        if c == 0:
            j = i
            while j < len(counts) and counts[j] == 0:
                j += 1
            r = j - i
            while r >= 3:
                put(3, 2); r -= 3
            put(r, 2)
            i = j
    return bits


def random_bytes(n):
    return bytes(rng.randrange(256) for _ in range(n))


def tobytes(bits):
    out = bytearray((len(bits) + 7) // 8)
    for k, b in enumerate(bits):
        out[k // 8] |= b << (k % 8)
    return bytes(out)


def random_counts(al, nsym, lowprob=True):
    nsym = max(nsym, 2)
    total = 1 << al
    counts = [0] * nsym
    present = [s for s in range(nsym) if rng.random() < 0.7]
    if len(present) < 2:
        present = rng.sample(range(nsym), 2)
    present.sort()
    left = total
    for s in present:
        if lowprob and rng.random() < 0.2 and left > len(present):
            counts[s] = -1
            left -= 1
    pos = [s for s in present if counts[s] != -1]
    if not pos:
        counts[present[0]] = 0
        pos = [present[0]]
        left += 1
    for _ in range(left):
        counts[rng.choice(pos)] += 1
    while counts and counts[-1] == 0:
        counts.pop()
    return counts


def fse_encode_weights(weights, counts, al):
    # Not an encoder: just random stream bytes after the header
    n = rng.randint(1, 40)
    stream = bytes(rng.randrange(256) for _ in range(n))
    if rng.random() < 0.9 and stream[-1] == 0:
        stream = stream[:-1] + bytes([rng.randrange(1, 256)])
    return stream


def mutate(b):
    b = bytearray(b)
    k = rng.randrange(4)
    if k == 0 and b:
        i = rng.randrange(len(b)); b[i] ^= 1 << rng.randrange(8)
    elif k == 1 and len(b) > 1:
        del b[rng.randrange(len(b)):]
    elif k == 2:
        b += bytes(rng.randrange(256) for _ in range(rng.randint(1, 4)))
    elif b:
        i = rng.randrange(len(b)); b[i] = rng.randrange(256)
    return bytes(b)


def gen_data():
    n = rng.choice([1, 2, 3, 4, 5, 10, 50, 100, 300, 1000, 3000])
    k = rng.choice([2, 3, 5, 16, 64, 200, 256])
    alpha = rng.sample(range(256), k)
    skew = rng.choice([0.5, 1.0, 2.0, 4.0])
    wts = [1.0 / (i + 1) ** skew for i in range(k)]
    return bytes(rng.choices(alpha, wts, k=n))


cases = []       # (kind, args...)
# 1. valid inputs from zstd's compressor, and their mutations
datas = [gen_data() for _ in range(N)]
comp = drive(['C 255 %d %s' % (rng.choice([11, 11, 12, 8, 6]), d.hex())
              for d in datas])
for d, c in zip(datas, comp):
    if not c.startswith('OK '):
        continue
    src = bytes.fromhex(c[3:])
    cases.append(('D', src, len(d), d))
    cases.append(('D', src, max(0, len(d) + rng.choice([-1, 1, 2])), None))
    for _ in range(3):
        cases.append(('D', mutate(src), len(d), None))
    cases.append(('S', src))
# 2. raw weight headers with random weights and streams
for _ in range(N):
    nsym = rng.randint(1, 128)
    w = [rng.choice([0, 1, 1, 2, 3, 4, 5, rng.randrange(16)])
         for _ in range(nsym)]
    nb = (nsym + 1) // 2
    hdr = bytes([127 + nsym]) + bytes(
        ((w[2*i] << 4) | (w[2*i+1] if 2*i+1 < nsym else rng.randrange(16)))
        for i in range(nb))
    stream = bytes(rng.randrange(256) for _ in range(rng.randint(1, 20)))
    src = hdr + stream
    cases.append(('S', src))
    cases.append(('D', src, rng.randint(0, 40), None))
# 3. FSE weight headers with random NCounts
for _ in range(N):
    al = rng.choice([5, 5, 6, 6, 7])
    nsym = rng.randint(1, 13)
    counts = random_counts(al, nsym)
    if not counts:
        continue
    bits = ncount_bits(counts, al)
    nc = tobytes(bits)
    cases.append(('N', nc + bytes(rng.randrange(256)
                                   for _ in range(rng.randint(0, 9)))))
    body = nc + fse_encode_weights(None, counts, al)
    if len(body) < 128:
        src = bytes([len(body)]) + body + bytes(
            rng.randrange(256) for _ in range(rng.randint(1, 10)))
        cases.append(('S', src))
        cases.append(('D', src, rng.randint(0, 30), None))
# 4. random NCounts with larger tables, and random bytes
for _ in range(N):
    al = rng.randint(5, 12)
    counts = random_counts(al, rng.randint(2, 60))
    if counts:
        nc = tobytes(ncount_bits(counts, al))
        cut = rng.choice([len(nc), len(nc), max(1, len(nc) - 1)])
        cases.append(('N', nc[:cut] + random_bytes(rng.randint(0, 3))))
    cases.append(('N', random_bytes(rng.randint(1, 12))))
    cases.append(('S', random_bytes(rng.randint(1, 40))))

# 5. crafted complete prefix codes of depth up to 12, with headers written
# raw (here) or by zstd's HUF_writeCTable_wksp, and streams encoded here
def random_lengths():
    maxlen = rng.choice([1, 2, 3, 5, 8, 10, 11, 11, 12, 12, 12])
    k = rng.choice([2, 3, 5, 13, 30, 100, 200, 256])
    deep = rng.random()
    leaves = [0]
    while len(leaves) < k:
        cand = [i for i, d in enumerate(leaves) if d < maxlen]
        if not cand:
            break
        if rng.random() < deep:
            i = max(cand, key=lambda i: leaves[i])
        else:
            i = rng.choice(cand)
        d = leaves.pop(i)
        leaves += [d + 1, d + 1]
    syms = rng.sample(range(256), len(leaves))
    lens = [0] * (max(syms) + 1)
    for s, d in zip(syms, leaves):
        lens[s] = d
    return lens


def huf_codes(lens):
    mb = max(lens)
    order = sorted((mb + 1 - d, s) for s, d in enumerate(lens) if d > 0)
    codes, start = {}, 0
    for x, s in order:
        nb = mb + 1 - x
        codes[s] = (start >> (mb - nb), nb)
        start += 1 << (mb - nb)
    assert start == 1 << mb
    return codes


def huf_encode(msg, codes):
    b = 1
    for s in msg:
        c, nb = codes[s]
        b = (b << nb) | c
    return b.to_bytes((b.bit_length() + 7) // 8, 'little')


def raw_header(lens):
    mb = max(lens)
    w = [mb + 1 - d if d else 0 for d in lens[:-1]]
    if not 1 <= len(w) <= 128:
        return None
    if len(w) % 2:
        w.append(rng.randrange(16))
    return bytes([127 + len(lens) - 1]) + bytes(
        (w[i] << 4) | w[i + 1] for i in range(0, len(w), 2))


trees = [random_lengths() for _ in range(N)]
written = drive(['W ' + bytes(t).hex() for t in trees])
for lens, wr in zip(trees, written):
    hdrs = [bytes.fromhex(wr[3:])] if wr.startswith('OK ') else []
    rh = raw_header(lens)
    if rh is not None:
        hdrs.append(rh)
    codes = huf_codes(lens)
    alpha = sorted(codes)
    for hdr in hdrs:
        cases.append(('S', hdr))
        m = rng.choice([0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 100, 1000])
        msg = rng.choices(alpha, k=m)
        st = huf_encode(msg, codes)
        cases.append(('D', hdr + st, m, bytes(msg)))
        cases.append(('D', hdr + st, max(0, m + rng.choice([-1, 1])), None))
        cases.append(('D', hdr + mutate(st), m, None))
        cases.append(('D', mutate(hdr) + st, m, None))
        if m and st[-1] < 0x80:
            # one spare bit set below the end flag: not consumed exactly
            b = bytearray(st)
            b[-1] = b[-1] * 2 + 1
            cases.append(('D', hdr + bytes(b), m, None))
# 6. FSE table descriptions with long runs of zero probabilities
for _ in range(N // 4):
    al = rng.randint(5, 9)
    nz = rng.randint(30, 200)
    counts = [-1, 0] + [0] * nz + [(1 << al) - 2]
    if len(counts) > 256:
        continue
    nc = tobytes(ncount_bits(counts, al))
    cases.append(('N', nc + bytes(rng.randrange(256)
                                   for _ in range(rng.randint(0, 3)))))
    cases.append(('N', nc[:rng.randrange(1, len(nc) + 1)]))
# 6b. descriptions one byte short whose last count is a -1 coded as a
# single 0 bit in the missing byte (an attempt to reach zstd's final check
# bitCount > 32, which seems to be unreachable: a position at the end of the
# input wraps before the last count is read)
for _ in range(N // 4):
    al = rng.randint(5, 9)
    for _ in range(100):
        counts = random_counts(al, rng.randint(2, 40))
        # make the total 2^al - 1 with the last count, then append a -1
        total = sum(1 if c == -1 else c for c in counts)
        if not counts or counts[-1] <= 1 or total != 1 << al:
            continue
        counts[-1] -= 1
        counts.append(-1)
        bits = ncount_bits(counts, al)
        if len(bits) % 8 == 1:
            cases.append(('N', tobytes(bits)[:-1]))
            break

# 7. a few large skewed inputs, so that zstd's encoder uses 12-bit codes
fib = [1, 1]
while len(fib) < 40:
    fib.append(fib[-1] + fib[-2])
bigs = []
for _ in range(max(1, N // 100)):
    k = rng.randint(14, 30)
    wts = [fib[min(i, 20)] for i in range(k)]
    alpha = rng.sample(range(256), k)
    bigs.append(bytes(rng.choices(alpha, wts, k=rng.randint(9000, 20000))))
for d, c in zip(bigs, drive(['C 255 12 ' + d.hex() for d in bigs])):
    if c.startswith('OK '):
        src = bytes.fromhex(c[3:])
        cases.append(('D', src, len(d), d))
        cases.append(('S', src))
        cases.append(('D', mutate(src), len(d), None))

# 9. FSE-compressed weights with chosen accuracy logs and normalized
# counts, extended with unused "less than 1" symbols up to a chosen maximum
# symbol, written by zstd's FSE_writeNCount and FSE_compress_usingCTable
def normalize(hist, al, msv):
    total = 1 << al
    n = sum(hist)
    counts = [max(1, h * total // n) if h else 0 for h in hist]
    for s in range(len(counts)):
        if counts[s] == 1 and rng.random() < 0.3:
            counts[s] = -1
    counts += [0] * (msv + 1 - len(counts))
    for s in range(len(hist), msv + 1):
        if s == msv or rng.random() < 0.1:
            counts[s] = -1
    used = sum(1 if c == -1 else c for c in counts)
    big = max(range(len(counts)), key=lambda s: counts[s])
    counts[big] += total - used
    return counts if counts[big] >= 1 else None


fcases = []
for _ in range(N):
    lens = random_lengths()
    mb = max(lens)
    w = [mb + 1 - d if d else 0 for d in lens[:-1]]
    if len(w) < 3 or max(w) > 12:
        continue
    hist = [0] * (max(w) + 1)
    for x in w:
        hist[x] += 1
    al = rng.choice([5, 6])
    lo = max(w)
    msv = rng.choice([lo, lo, 11, 12, 13, 90, 91, 92, 93, 200, 255])
    if msv < lo:
        msv = lo
    counts = normalize(hist, al, msv)
    if counts is None:
        continue
    fcases.append((lens, al, counts, bytes(w)))
outs = drive(['F %d %d %s %s' % (al, len(counts) - 1,
                                 ' '.join(map(str, counts)), w.hex())
              for lens, al, counts, w in fcases])
for (lens, al, counts, w), o in zip(fcases, outs):
    if not o.startswith('OK '):
        continue
    blk = bytes.fromhex(o[3:])
    if len(blk) >= 128:
        continue
    hdr = bytes([len(blk)]) + blk
    codes = huf_codes(lens)
    m = rng.choice([1, 5, 50])
    msg = rng.choices(sorted(codes), k=m)
    cases.append(('S', hdr))
    cases.append(('D', hdr + huf_encode(msg, codes), m, bytes(msg)))

# 10. tree descriptions that zstd accepts only because its reading of the
# FSE table description wraps around: three found by wrapsearch.py, and a
# short search for more
for h in ['08700648e2eab2712a', '07505ac089ccbe8a', '07004a493279f307']:
    cases.append(('S', bytes.fromhex(h)))
    cases.append(('D', bytes.fromhex(h) + bytes([rng.randrange(1, 256)]),
                  rng.randint(0, 9), None))
for _ in range(20 * N):
    isize = rng.randint(2, 24)
    body = bytearray(rng.randrange(256) for _ in range(isize))
    body[0] = (body[0] & 0xF0) | rng.choice([0, 1])
    try:
        ref.fse_weight_block(True, bytes(body))
        ref.fse_ncount(False, 15, 256, bytes(body))
        continue
    except ref.Fail as e:
        if str(e) != 'NCount beyond the input':
            continue
    hdr = bytes([isize]) + bytes(body)
    cases.append(('S', hdr))
    cases.append(('D', hdr + bytes([rng.randrange(1, 256)]),
                  rng.randint(0, 9), None))

# 8. the example of RFC 8878 section 4.2.2 (weights of Table 24): the
# stream as printed decodes to 0154 (erratum 8195 swaps the codes of 4 and
# 5 in Table 26); the corrected stream decodes to 0145
ex = bytes.fromhex('84432010')
cases.append(('D', ex + bytes([0x10, 0x0d]), 4, bytes([0, 1, 5, 4])))
cases.append(('D', ex + bytes([0x01, 0x0d]), 4, bytes([0, 1, 4, 5])))

lines = []
for c in cases:
    if c[0] == 'D':
        lines.append('D %d %s' % (c[2], c[1].hex()))
    else:
        lines.append('%s %s' % (c[0], c[1].hex()))
res = drive(lines)

def mirror(c, zstd):
    kind = c[0]
    try:
        if kind == 'D':
            got = ref.huf_decompress1x1(zstd, c[1], c[2])
            return 'OK ' + got.hex()
        elif kind == 'N':
            counts, al, n = ref.fse_ncount(zstd, 15, 256, c[1])
            return 'OK %d %d %d %s' % (n, len(counts) - 1, al,
                                       ' '.join(map(str, counts)))
        else:
            w, mb, n = ref.huf_weights(zstd, c[1])
            return 'OK %d %d %d %s' % (n, len(w), mb, ' '.join(map(str, w)))
    except ref.Fail as e:
        return 'ERR (%s)' % e


# zstd must agree exactly with the zstd dialect of the mirror, and with the
# RFC reading except where the RFC reading rejects the input for one of the
# reasons below (see rfc8878_ref.py).
allowed = ['ERR (%s)' % e for e in
           ['NCount beyond the input', 'tree too deep',
            'too many symbols in NCount']]
bad = 0
stats = {}
for c, r in zip(cases, res):
    kind = c[0]
    r = r.strip()
    dial = mirror(c, True).strip()
    rfc = mirror(c, False).strip()
    zok = r.startswith('OK')
    stats[(kind, zok)] = stats.get((kind, zok), 0) + 1
    if zok != dial.startswith('OK') or (zok and r != dial):
        bad += 1
        if bad <= 10:
            print('MISMATCH', kind, c[1].hex()[:120],
                  c[2] if kind == 'D' else '')
            print('   zstd   :', r[:150])
            print('   dialect:', dial[:150])
    if rfc != dial:
        key = (kind, 'rfc ' + rfc[:3].strip(), 'dialect ' + dial[:3].strip(),
               rfc[4:] if rfc.startswith('ERR') else '')
        stats[key] = stats.get(key, 0) + 1
        if rfc.startswith('OK') or rfc not in allowed:
            bad += 1
            print('RFC DEVIATION', kind, c[1].hex()[:120])
            print('   rfc    :', rfc[:150])
            print('   dialect:', dial[:150])
    if kind == 'D' and zok and c[3] is not None and r[3:] != c[3].hex():
        print('ROUND TRIP FAIL', c[1].hex()[:100])
print('cases', len(cases), 'mismatches', bad)
for k, v in sorted(stats.items(), key=str):
    print('  ', k, v)
print('features', sorted(ref.FEATURES))
