# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# A Python mirror of the HOL Light specification of DEFLATE decoding
# (common/rfc1951.ml). Each function corresponds to a HOL definition or
# inductive relation, and is written to follow it rather than to be fast.
# decode(data) returns (output, number of bytes used) or None.

BASE_LEN = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31,
            35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258]
EXTRA_LEN = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2,
             3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0]
BASE_DIST = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193,
             257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145,
             8193, 12289, 16385, 24577]
EXTRA_DIST = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6,
              7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13]
CLEN_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14,
              1, 15]
FIXED_LL = [8 if s < 144 else 9 if s < 256 else 7 if s < 280 else 8
            for s in range(288)]
FIXED_DL = [5] * 32


class Fail(Exception):
    pass


# Test instrumentation: notable events in the last decode, and why the last
# failing decode failed.
FEATURES = set()
LAST_FAIL = None


def note(x):
    FEATURES.add(x)


def bit(data, i):                 # deflate_bit
    # Every rule of the HOL relations that reads a bit also requires it to
    # be within the input, so reading past the end means the rule fails.
    if i >= 8 * len(data):
        raise Fail('out of input')
    return (data[i // 8] >> (i % 8)) & 1


def bits(data, p, n):             # deflate_bits: least significant first
    return sum(bit(data, p + i) << i for i in range(n))


def codebits(data, p, n):         # deflate_codebits: most significant first
    return sum(bit(data, p + i) << (n - 1 - i) for i in range(n))


def huffman_code(lens, s):        # huffman_code
    L = lens[s]
    return (sum(2 ** (L - lens[t]) for t in range(len(lens))
                if lens[t] != 0 and lens[t] < L) +
            sum(1 for t in range(s) if lens[t] == L))


def huffman_kraft(lens):
    return sum(2 ** (15 - x) for x in lens if x != 0)


def huffman_ok(lens):
    k = huffman_kraft(lens)
    return k <= 2 ** 15 and (k == 2 ** 15 or all(x <= 1 for x in lens))


class Code:
    """The symbols decodable with code lengths lens, by their code bits."""
    def __init__(self, lens):
        self.lens = lens
        self.table = {}
        for s in range(len(lens)):
            if lens[s] != 0:
                key = (lens[s], huffman_code(lens, s))
                # the relation would not be functional for a non prefix-free
                # code; such codes are only used after being rejected
                self.table.setdefault(key, []).append(s)


def huffman_decode(data, code, p):
    """The (s, q) with huffman_decode l lens p s q, which is unique for a
    prefix-free code; Fail if there is none."""
    found = []
    for L in range(1, 16):
        if p + L <= 8 * len(data):
            found += [(s, p + L) for s in
                      code.table.get((L, codebits(data, p, L)), [])]
    if len(found) == 0:
        raise Fail('no symbol')
    if len(found) > 1:
        raise AssertionError('code is not prefix-free')
    return found[0]


def lz77_copy(out, dist, n):
    for _ in range(n):
        out.append(out[len(out) - dist])


def need(c, why):
    if not c:
        raise Fail(why)


def deflate_codes(data, ll, dl, out, p):
    """The relation deflate_codes l ll dl (out,p) r, as a function."""
    while True:
        s, q = huffman_decode(data, ll, p)
        if s == 256:
            return q
        if s < 256:
            out.append(s)
            p = q
            continue
        need(257 <= s <= 285, 'bad length symbol')
        i = s - 257
        p1 = q
        d, p2 = huffman_decode(data, dl, p1 + EXTRA_LEN[i])
        need(d < 30, 'bad distance symbol')
        q = p2 + EXTRA_DIST[d]
        need(q <= 8 * len(data), 'out of input')
        length = BASE_LEN[i] + bits(data, p1, EXTRA_LEN[i])
        dist = BASE_DIST[d] + bits(data, p2, EXTRA_DIST[d])
        need(dist <= len(out), 'distance too far back')
        if length > dist:
            note('overlapping copy')
        if i == 27 and length == 258:
            note('length 258 as 227+31')
        if dist > 16384:
            note('long distance')
        lz77_copy(out, dist, length)
        p = q


def deflate_stored(data, out, p):
    a = 8 * ((p + 7) // 8)
    n = bits(data, a, 16) if a + 16 <= 8 * len(data) else None
    need(n is not None and a + 32 + 8 * n <= 8 * len(data), 'out of input')
    need(bits(data, a + 16, 16) == 65535 - n, 'NLEN mismatch')
    if n == 0:
        note('empty stored block')
    out.extend(data[a // 8 + 4 + i] for i in range(n))
    return a + 32 + 8 * n


def deflate_lengths(data, cl, n, p):
    lens = []
    while len(lens) < n:
        s, q = huffman_decode(data, cl, p)
        if s < 16:
            lens.append(s)
            p = q
            continue
        if s == 16:
            need(lens != [], 'repeat with no previous length')
            x, e, k = lens[-1], 2, 3 + bits(data, q, 2)
        elif s == 17:
            x, e, k = 0, 3, 3 + bits(data, q, 3)
        else:
            x, e, k = 0, 7, 11 + bits(data, q, 7)
        need(q + e <= 8 * len(data), 'out of input')
        need(len(lens) + k <= n, 'too many lengths')
        lens += [x] * k
        p = q + e
    return lens, p


def deflate_dynamic(data, out, p):
    need(p + 14 <= 8 * len(data), 'out of input')
    nlen = 257 + bits(data, p, 5)
    ndist = 1 + bits(data, p + 5, 5)
    ncode = 4 + bits(data, p + 10, 4)
    need(nlen <= 286 and ndist <= 30, 'bad counts')
    need(p + 14 + 3 * ncode <= 8 * len(data), 'out of input')
    cl = [0] * 19
    for i in range(19):
        cl[CLEN_ORDER[i]] = bits(data, p + 14 + 3 * i, 3) if i < ncode else 0
    need(huffman_kraft(cl) == 2 ** 15, 'incomplete code length code')
    lens, q = deflate_lengths(data, Code(cl), nlen + ndist,
                              p + 14 + 3 * ncode)
    need(lens[256] != 0, 'no end-of-block code')
    ll, dl = lens[:nlen], lens[nlen:]
    need(huffman_ok(ll), 'bad literal/length code')
    need(huffman_ok(dl), 'bad distance code')
    if huffman_kraft(ll) < 2 ** 15:
        note('single literal/length code')
    if huffman_kraft(dl) == 0:
        note('no distance codes')
    elif huffman_kraft(dl) < 2 ** 15:
        note('single distance code')
    if nlen == 286:
        note('286 literal/length codes')
    if ncode == 19:
        note('19 code length codes')
    return deflate_codes(data, Code(ll), Code(dl), out, q)


FIXED = None


def deflate_block(data, btype, out, p):
    global FIXED
    if btype == 0:
        return deflate_stored(data, out, p)
    if btype == 1:
        if FIXED is None:
            FIXED = (Code(FIXED_LL), Code(FIXED_DL))
        return deflate_codes(data, FIXED[0], FIXED[1], out, p)
    if btype == 2:
        return deflate_dynamic(data, out, p)
    raise Fail('block type 3')


def decode(data):
    """deflate_decode: (out, n) or None."""
    global LAST_FAIL
    FEATURES.clear()
    LAST_FAIL = None
    out, p = [], 0
    try:
        while True:
            need(p + 3 <= 8 * len(data), 'out of input')
            final = bit(data, p)
            q = deflate_block(data, bits(data, p + 1, 2), out, p + 3)
            p = q
            if final:
                return bytes(out), (p + 7) // 8
    except Fail as e:
        LAST_FAIL = str(e)
        return None
