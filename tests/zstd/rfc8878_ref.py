# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# A Python mirror of common/rfc8878.ml, the HOL Light specification of
# zstd's Huffman-coded literals (RFC 8878, sections 4.1, 4.2 and 3.1.1.3.1):
# FSE table descriptions and decoding tables, Huffman tree descriptions,
# Huffman-coded streams and literals in one stream or in four. Each
# function follows the definition or inductive relation of the same name,
# to be read side by side with it, not to be fast. Where the HOL definition
# is a relation, the function computes the result that the relation
# determines, raising Fail when there is none.
#
# The flag zstd selects the RFC (False) or zstd 1.5.7 (True); see the HOL
# file for the differences.


class Fail(Exception):
    pass


FEATURES = set()


def note(x):
    FEATURES.add(x)


def bitsize(n):
    return n.bit_length()


# ---------------------------------------------------------------------------
# Bits. Bits past the end of the list read as 0.
# ---------------------------------------------------------------------------

def zstd_bit(l, i):
    return i < 8 * len(l) and (l[i // 8] >> (i % 8)) & 1 == 1


def zstd_bits(l, p, n):          # sum of 2^i * zstd_bit l (p + i), i < n
    return (int.from_bytes(bytes(l), 'little') >> p) % 2**n


def zstd_sublist(l, a, n):
    assert a + n <= len(l)
    return l[a:a + n]


# ---------------------------------------------------------------------------
# Backward bitstreams. zstd_end gives the r with zstd_end st r.
# ---------------------------------------------------------------------------

def zstd_end(st):
    if len(st) == 0:
        raise Fail('empty stream')
    if st[-1] == 0:
        raise Fail('last byte of stream is 0')
    return 8 * (len(st) - 1) + bitsize(st[-1]) - 1


def zstd_back(st, q, k):
    return (2**k * zstd_bits(st, 0, q)) // 2**q


# ---------------------------------------------------------------------------
# FSE table descriptions (section 4.1.1).
# ---------------------------------------------------------------------------

def fse_field(l, pts, p):
    nb = bitsize(pts + 1)
    small = 2**nb - (pts + 2)
    v = zstd_bits(l, p, nb)
    if v % 2**(nb - 1) < small:
        return v % 2**(nb - 1), p + nb - 1
    elif v < 2**(nb - 1):
        return v, p + nb
    else:
        return v - small, p + nb


def fse_points(v):
    return 1 if v == 0 else v - 1


def fse_inside(zstd, l, q):
    return zstd or q <= 8 * len(l)


def fse_reload(zstd, l, p):
    w = 8 * max(len(l), 8)
    if zstd and w <= p:
        note('NCount wrap')
        return w - 32 + (p - w) % 32
    return p


def check_inside(zstd, l, q):
    if not fse_inside(zstd, l, q):
        raise Fail('NCount beyond the input')


# fse_zeros zstd l (k,z,p) (z',q): returns (z',q).

def fse_zeros(zstd, l, k, z, p):
    while True:
        f = zstd_bits(l, p, 2)
        check_inside(zstd, l, p + 2)
        if f < 3:
            return z + f, fse_reload(zstd, l, p + 2)
        note('repeat 3')
        if k < 11:
            k, z, p = k + 1, z + 3, p + 2
        else:
            note('12 repeats')
            k, z, p = 0, z + 3, fse_reload(zstd, l, p + 2)


# fse_counts zstd l n (pts,cs,p) (cs',q): returns (cs',q).

def fse_counts(zstd, l, n, pts, cs, p):
    while True:
        if not len(cs) < n:
            raise Fail('too many symbols in NCount')
        v, q = fse_field(l, pts, p)
        check_inside(zstd, l, q)
        if fse_points(v) == pts:
            return cs + [v - 1], q
        elif v != 1 and fse_points(v) < pts:
            pts, cs, p = pts - fse_points(v), cs + [v - 1], \
                fse_reload(zstd, l, q)
        elif v == 1:
            note('zero prob')
            z, q2 = fse_zeros(zstd, l, 0, 0, fse_reload(zstd, l, q))
            cs, p = cs + [0] * (z + 1), q2
        else:
            raise Fail('NCount overshoots the total')


def fse_ncount(zstd, maxalog, n, l):
    alog = zstd_bits(l, 0, 4) + 5
    if not alog <= maxalog:
        raise Fail('accuracy log too large')
    cs, q = fse_counts(zstd, l, n, 2**alog, [], 4)
    if not q <= 8 * len(l):
        raise Fail('NCount beyond the input')
    return cs, alog, (q + 7) // 8


# ---------------------------------------------------------------------------
# FSE decoding tables (section 4.1.1).
# ---------------------------------------------------------------------------

def fse_step(alog):
    return 2**alog // 2 + 2**alog // 8 + 3


def fse_lowprob(cs):
    return [s for s in range(len(cs)) if cs[s] == -1]


def fse_spread(cs, alog):
    low = fse_lowprob(cs)
    cells = [u for u in [(j * fse_step(alog)) % 2**alog
                         for j in range(2**alog)]
             if u < 2**alog - len(low)]
    syms = [s for s in range(len(cs)) for _ in range(max(cs[s], 0))]
    assert len(cells) == len(syms)
    return list(zip(cells, syms)) + \
        list(zip([2**alog - 1 - j for j in range(len(low))], low))


def fse_symbol(cs, alog, u):
    return dict(fse_spread(cs, alog))[u]


def fse_next(cs, alog, u):
    s = fse_symbol(cs, alog, u)
    return (1 if cs[s] == -1 else cs[s]) + \
        sum(1 for v in range(u) if fse_symbol(cs, alog, v) == s)


def fse_nbits(cs, alog, u):
    return alog + 1 - bitsize(fse_next(cs, alog, u))


def fse_base(cs, alog, u):
    return 2**fse_nbits(cs, alog, u) * fse_next(cs, alog, u) - 2**alog


# The same, for all states at once, as a list of (symbol, nbits, base).

def fse_table(cs, alog):
    sym = dict(fse_spread(cs, alog))
    seen = {}
    table = []
    for u in range(2**alog):
        s = sym[u]
        nxt = (1 if cs[s] == -1 else cs[s]) + seen.get(s, 0)
        seen[s] = seen.get(s, 0) + 1
        nb = alog + 1 - bitsize(nxt)
        table.append((s, nb, 2**nb * nxt - 2**alog))
    return table


# ---------------------------------------------------------------------------
# FSE-compressed Huffman weights (section 4.2.1.2).
# fse_weights cs alog st (s,s',q,ws) w: returns w.
# ---------------------------------------------------------------------------

def fse_weights(cs, alog, st, s, s2, q, ws):
    table = fse_table(cs, alog)
    while True:
        if not len(ws) + 2 <= 255:
            note('too many weights')
            raise Fail('too many weights')
        sym, nb, base = table[s]
        if q < nb:
            note('weights end at state %d' % (len(ws) % 2 + 1))
            if len(ws) + 2 >= 254:
                note('%d weights' % (len(ws) + 2))
            return ws + [sym, table[s2][0]]
        s, s2, q, ws = s2, base + zstd_back(st, q, nb), q - nb, ws + [sym]


def fse_weight_block(zstd, blk):
    cs, alog, m = fse_ncount(zstd, 6, 256 if zstd else 12, blk)
    if zstd and not len(cs) <= (12 if alog == 6 else 92):
        raise Fail('too many symbols for the workspace')
    st = zstd_sublist(blk, m, len(blk) - m)
    r = zstd_end(st)
    if not 2 * alog <= r:
        raise Fail('initial states beyond the stream')
    return fse_weights(cs, alog, st, zstd_back(st, r, alog),
                       zstd_back(st, r - alog, alog), r - 2 * alog, [])


# ---------------------------------------------------------------------------
# Huffman tree descriptions (section 4.2.1).
# huf_header zstd l w h: returns (w,h).
# ---------------------------------------------------------------------------

def huf_header(zstd, l):
    if len(l) == 0:
        raise Fail('no tree description')
    b = l[0]
    if 128 <= b:
        h = 1 + (b - 126) // 2
        if not h <= len(l):
            raise Fail('raw weights beyond the input')
        note('raw weights')
        return [l[1 + i // 2] // 16 if i % 2 == 0 else l[1 + i // 2] % 16
                for i in range(b - 127)], h
    else:
        h = 1 + b
        if not h <= len(l):
            raise Fail('FSE weights beyond the input')
        note('FSE weights')
        return fse_weight_block(zstd, zstd_sublist(l, 1, h - 1)), h


# huf_weights zstd l ws ml h: returns (ws,ml,h).

def huf_weights(zstd, l):
    w, h = huf_header(zstd, l)
    total = sum(2**(x - 1) for x in w if x != 0)
    if total == 0:
        raise Fail('all weights zero')
    ml = bitsize(total)
    if not ml <= (12 if zstd else 11):
        raise Fail('tree too deep')
    rest = 2**ml - total
    k = bitsize(rest) - 1
    if rest != 2**k:
        raise Fail('last weight not a power of 2')
    ws = w + [k + 1]
    if 1 not in ws:
        raise Fail('no code of the maximum length')
    note('ml %d' % ml)
    return ws, ml, h


# ---------------------------------------------------------------------------
# Prefix codes (section 4.2.1.3).
# ---------------------------------------------------------------------------

def huf_code(ws, s):
    return sum(2**(ws[t] - 1) for t in range(len(ws))
               if ws[t] != 0 and (ws[t] < ws[s] or ws[t] == ws[s] and t < s)) \
        // 2**(ws[s] - 1)


# The same, for all symbols at once: the states in order of (weight, symbol).

def huf_codes(ws):
    codes, start = {}, 0
    for x, s in sorted((ws[s], s) for s in range(len(ws)) if ws[s] != 0):
        codes[s] = start // 2**(x - 1)
        start += 2**(x - 1)
    return codes


def huf_bits(ws, ml, out):
    codes = huf_codes(ws)
    v, n = 0, 0
    for c in reversed(out):
        v, n = 2**n * codes[c] + v, (ml + 1 - ws[c]) + n
    return v, n


# ---------------------------------------------------------------------------
# Huffman-coded streams (section 4.2.2). huf_stream ws ml st out, for out of
# length n: returns out, found by reading the codes from the top down and
# then checked against the definition.
# ---------------------------------------------------------------------------

def huf_stream(ws, ml, st, n):
    r = zstd_end(st)
    bits = zstd_bits(st, 0, r)
    codes = {(ml + 1 - ws[s], c): s for s, c in huf_codes(ws).items()}
    top = format(bits, 'b').zfill(r) if r else ''   # most significant first
    out, q = [], 0
    for _ in range(n):
        for nb in range(1, ml + 1):
            if q + nb <= r and (nb, int(top[q:q + nb], 2)) in codes:
                out.append(codes[(nb, int(top[q:q + nb], 2))])
                q += nb
                break
        else:
            raise Fail('no code matches the stream')
    if not all(c < len(ws) and ws[c] != 0 for c in out):
        raise Fail('symbol without a code')
    v, m = huf_bits(ws, ml, out)
    if not (m == r and bits == v):
        raise Fail('stream not consumed exactly')
    return bytes(out)


# ---------------------------------------------------------------------------
# Huffman-coded literals in a single stream: returns the n bytes out with
# huf_decompress1x1 zstd l out.
# ---------------------------------------------------------------------------

def huf_decompress1x1(zstd, l, n):
    ws, ml, h = huf_weights(zstd, l)
    if not h < len(l):
        raise Fail('no stream after the tree description')
    return huf_stream(ws, ml, zstd_sublist(l, h, len(l) - h), n)


# ---------------------------------------------------------------------------
# Huffman-coded literals in four streams: returns the n bytes out with
# huf_streams4 zstd ws ml blk out, for the block blk after the tree
# description, and with huf_decompress4x1 zstd l out.
# ---------------------------------------------------------------------------

def huf_jump(blk, k):
    return blk[2 * k] + 256 * blk[2 * k + 1]


def huf_streams4(zstd, ws, ml, blk, n):
    if not 6 <= len(blk):
        raise Fail('no jump table')
    s1, s2, s3 = huf_jump(blk, 0), huf_jump(blk, 1), huf_jump(blk, 2)
    q = (n + 3) // 4
    a4 = 6 + s1 + s2 + s3
    if not a4 <= len(blk):
        raise Fail('streams past the end of the block')
    if not 3 * q <= n:
        raise Fail('no fourth segment')
    if zstd and not 6 <= n:
        raise Fail('fewer than 6 bytes in four streams')
    note('four streams')
    return (huf_stream(ws, ml, zstd_sublist(blk, 6, s1), q) +
            huf_stream(ws, ml, zstd_sublist(blk, 6 + s1, s2), q) +
            huf_stream(ws, ml, zstd_sublist(blk, 6 + s1 + s2, s3), q) +
            huf_stream(ws, ml, zstd_sublist(blk, a4, len(blk) - a4),
                       n - 3 * q))


def huf_decompress4x1(zstd, l, n):
    ws, ml, h = huf_weights(zstd, l)
    if not h < len(l):
        raise Fail('no stream after the tree description')
    return huf_streams4(zstd, ws, ml, zstd_sublist(l, h, len(l) - h), n)
