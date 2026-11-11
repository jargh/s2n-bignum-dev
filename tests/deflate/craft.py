# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Crafted DEFLATE streams that exercise the corners of the format, encoded
# with the canonical codes as defined in the spec mirror, and compared with
# zlib's raw inflate.  usage: python3 -I craft.py [SEED] [N]
import os, random, sys, zlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rfc1951_ref as ref

rng = random.Random(1)


class Writer:
    def __init__(self):
        self.bits = []

    def put(self, v, n):              # least significant bit first
        self.bits += [(v >> i) & 1 for i in range(n)]

    def code(self, v, n):             # most significant bit first
        self.bits += [(v >> (n - 1 - i)) & 1 for i in range(n)]

    def align(self):
        while len(self.bits) % 8:
            self.bits.append(rng.randrange(2))

    def data(self):
        b = self.bits + [rng.randrange(2) for _ in range(-len(self.bits) % 8)]
        return bytes(sum(b[i + j] << j for j in range(8))
                     for i in range(0, len(b), 8))


def random_lengths(n, required=(), maxlen=15):
    """Code lengths for n symbols: a random complete code (by splitting a
    random leaf of a binary tree), then sometimes damaged."""
    nsyms = min(n, rng.choice([1, 2, 3, 5, 10, 30, n]))
    leaves = [0]
    while len(leaves) < nsyms:
        cand = [i for i, d in enumerate(leaves) if d < maxlen]
        if not cand:
            break
        i = rng.choice(cand)
        d = leaves.pop(i)
        leaves += [d + 1, d + 1]
    syms = list(required) + rng.sample([s for s in range(n)
                                        if s not in required],
                                       max(0, len(leaves) - len(required)))
    lens = [0] * n
    for s, d in zip(syms, leaves):
        lens[s] = max(d, 1)
    r = rng.randrange(10)
    if r == 0:                                        # damage a length
        s = rng.randrange(n)
        lens[s] = rng.randrange(maxlen + 1)
    elif r == 1:                                      # drop a symbol
        s = rng.choice([s for s in range(n) if lens[s]] or [0])
        lens[s] = 0
    return lens


def put_symbol(w, lens, s):
    w.code(ref.huffman_code(lens, s), lens[s])


def length_code(length):
    for i in range(28, -1, -1):
        if ref.BASE_LEN[i] <= length and (
                length - ref.BASE_LEN[i] < 2 ** ref.EXTRA_LEN[i]):
            if i == 28 and length != 258:
                continue
            return 257 + i, length - ref.BASE_LEN[i], ref.EXTRA_LEN[i]
    raise ValueError


def dist_code(dist):
    for d in range(29, -1, -1):
        top = ref.BASE_DIST[d] + 2 ** ref.EXTRA_DIST[d]
        if ref.BASE_DIST[d] <= dist < top:
            return d, dist - ref.BASE_DIST[d], ref.EXTRA_DIST[d]
    raise ValueError


def put_data(w, ll, dl, outlen, nsym):
    """Random literals and length/distance pairs, then end of block; the
    symbols are chosen among those that have codes (mostly)."""
    lit = [s for s in range(len(ll)) if ll[s] and s < 256]
    lsym = [s for s in range(len(ll)) if ll[s] and s > 256]
    dsym = [d for d in range(len(dl)) if dl[d]]
    for _ in range(nsym):
        r = rng.randrange(10)
        if r < 5 and lit:
            put_symbol(w, ll, rng.choice(lit))
            outlen += 1
        elif r < 9 and lsym and dsym:
            s = rng.choice(lsym)
            i = s - 257
            if i >= 29:
                put_symbol(w, ll, s)          # invalid symbol 286/287
                return outlen
            put_symbol(w, ll, s)
            w.put(rng.randrange(2 ** ref.EXTRA_LEN[i]), ref.EXTRA_LEN[i])
            d = rng.choice(dsym)
            if rng.randrange(8) == 0 or d >= 30:
                put_symbol(w, dl, d)
                w.put(rng.randrange(2 ** ref.EXTRA_DIST[min(d, 29)]),
                      ref.EXTRA_DIST[min(d, 29)])
            else:
                # choose extra bits to make the distance in range, mostly
                ex = ref.EXTRA_DIST[d]
                top = min(2 ** ex - 1, max(0, outlen - ref.BASE_DIST[d]))
                put_symbol(w, dl, d)
                w.put(rng.randrange(top + 1) if rng.randrange(10) else
                      rng.randrange(2 ** ex), ex)
            outlen += ref.BASE_LEN[i]
        elif rng.randrange(20) == 0:
            break                             # missing end of block
    if ll[256] if len(ll) > 256 else False:
        put_symbol(w, ll, 256)
    return outlen


def put_lengths(w, cl, lens):
    """Run-length code lens with the code length code cl, mostly validly."""
    i = 0
    prev = None
    while i < len(lens):
        x = lens[i]
        run = 1
        while i + run < len(lens) and lens[i + run] == x:
            run += 1
        r = rng.randrange(20)
        if r == 0:                                    # junk repeat
            s = rng.choice([16, 17, 18])
            if cl[s]:
                put_symbol(w, cl, s)
                w.put(rng.randrange(2 ** {16: 2, 17: 3, 18: 7}[s]),
                      {16: 2, 17: 3, 18: 7}[s])
                i += 3
                continue
        if x == 0 and run >= 11 and cl[18]:
            k = min(run, 138)
            put_symbol(w, cl, 18)
            w.put(k - 11, 7)
            i += k
        elif x == 0 and run >= 3 and cl[17]:
            k = min(run, 10)
            put_symbol(w, cl, 17)
            w.put(k - 3, 3)
            i += k
        elif prev == x and run >= 3 and cl[16]:
            k = min(run, 6)
            put_symbol(w, cl, 16)
            w.put(k - 3, 2)
            i += k
        elif cl[x]:
            put_symbol(w, cl, x)
            i += 1
        else:
            put_symbol(w, cl, rng.choice([s for s in range(19) if cl[s]]
                                         or [0])) if any(cl) else None
            i += 1
        prev = x


def dynamic_block(w, outlen):
    nlen = rng.choice([257, 258, 270, 286, 286, 287])
    ndist = rng.choice([1, 2, 5, 30, 30, 31])
    ll = random_lengths(nlen, required=(256,))
    dl = random_lengths(ndist)
    if rng.randrange(8) == 0:
        dl = [0] * ndist
    lens = ll + dl
    cl = random_lengths(19, required=sorted(set(lens) & set(range(16))),
                        maxlen=7)
    ncode = max([i + 1 for i in range(19) if cl[ref.CLEN_ORDER[i]]] + [4])
    if rng.randrange(10) == 0:
        ncode = rng.randrange(4, 20)
    w.put(nlen - 257, 5)
    w.put(ndist - 1, 5)
    w.put(ncode - 4, 4)
    for i in range(ncode):
        w.put(cl[ref.CLEN_ORDER[i]], 3)
    put_lengths(w, cl, lens)
    return put_data(w, ll, dl, outlen, rng.randrange(1, 30))


def stream():
    w = Writer()
    outlen = 0
    nblocks = rng.randrange(1, 4)
    for b in range(nblocks):
        w.put(1 if b == nblocks - 1 else 0, 1)
        t = rng.choice([0, 1, 2, 2, 2, 3])
        w.put(t, 2)
        if t == 0:
            w.align()
            n = rng.choice([0, 1, 5, 300])
            w.put(n, 16)
            w.put(65535 - n if rng.randrange(10) else rng.randrange(65536), 16)
            for _ in range(n):
                w.put(rng.randrange(256), 8)
            outlen += n
        elif t == 1:
            outlen = put_data(w, ref.FIXED_LL, ref.FIXED_DL, outlen,
                              rng.randrange(1, 30))
        elif t == 2:
            outlen = dynamic_block(w, outlen)
    return w.data()


def zlib_decode(data):
    d = zlib.decompressobj(-15)
    try:
        out = d.decompress(data)
    except zlib.error:
        return None
    if not d.eof:
        return None
    return out, len(data) - len(d.unused_data)


if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    rng.seed(seed)
    ok = bad = 0
    mism = []
    seen, why = {}, {}
    for t in range(N):
        data = stream()
        a, b = ref.decode(data), zlib_decode(data)
        if a != b:
            mism.append((data, a and len(a[0]), b and len(b[0])))
        elif a:
            ok += 1
            for f in ref.FEATURES:
                seen[f] = seen.get(f, 0) + 1
        else:
            bad += 1
            why[ref.LAST_FAIL] = why.get(ref.LAST_FAIL, 0) + 1
    print('accepted', ok, 'rejected', bad, 'MISMATCHES', len(mism))
    print('accepted with:', sorted(seen.items()))
    print('rejected for:', sorted(why.items()))
    for m in mism[:5]:
        print(m[0][:48].hex(), m[1], m[2])
