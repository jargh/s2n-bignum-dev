# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Generate hol_tests.ml: small Huffman-coded literals of each kind, with the
# output that zstd gives, for checking with HUF_DECOMPRESS1X1_RULE in
# rfc8878_eval.ml, in the zstd reading and, where the RFC accepts the input
# too, in the RFC reading; and literals in four streams, for checking with
# HUF_DECOMPRESS4X1_RULE, with the output of zstd without its fast decoding
# (or of the mirror, for an input that only the RFC accepts). ZHUF_RUN must
# have the decoding of four streams (zhuf_run_direct).
# usage: python3 -I -B make_hol_tests.py ZHUF_RUN > hol_tests.ml
import os, random, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rfc8878_ref as ref

run = sys.argv[1]
rng = random.Random(5)


def drive(lines):
    p = subprocess.run([run], input='\n'.join(lines) + '\n',
                       capture_output=True, text=True)
    return p.stdout.splitlines()


def codes_stream(lens, msg):
    mb = max(lens)
    ws = [mb + 1 - d if d else 0 for d in lens]
    v, n = ref.huf_bits(ws, mb, msg)
    b = (1 << n) | v
    return b.to_bytes((b.bit_length() + 7) // 8, 'little')


def raw_header(lens):
    mb = max(lens)
    w = [mb + 1 - d if d else 0 for d in lens[:-1]]
    if len(w) % 2:
        w.append(0)
    return bytes([127 + len(lens) - 1]) + bytes(
        (w[i] << 4) | w[i + 1] for i in range(0, len(w), 2))


def fse_header(lens, alog, counts):
    mb = max(lens)
    w = bytes(mb + 1 - d if d else 0 for d in lens[:-1])
    o = drive(['F %d %d %s %s' % (alog, len(counts) - 1,
                                  ' '.join(map(str, counts)), w.hex())])[0]
    assert o.startswith('OK '), o
    blk = bytes.fromhex(o[3:])
    return bytes([len(blk)]) + blk


cases = []
cases.append(('RFC 8878 example (erratum 8195)',
              bytes.fromhex('8443201001 0d'.replace(' ', '')), 4))
cases.append(('RFC 8878 example as printed',
              bytes.fromhex('8443201010 0d'.replace(' ', '')), 4))
cases.append(('two codes, no output', bytes([0x80, 0x10, 0x01]), 0))
cases.append(('two codes', bytes([0x80, 0x10, 0x0d]), 3))
# depths 1 to 12, raw: 12-bit codes, which only zstd allows
lens12 = list(range(1, 13)) + [12]
msg = [0, 12, 11, 5, 0, 0, 1]
cases.append(('12-bit codes', raw_header(lens12) + codes_stream(lens12, msg),
              len(msg)))
# FSE-compressed weights, with a "less than 1" probability
lens8 = [2, 2, 3, 3, 3, 4, 5, 5]
msg = [rng.choice(range(8)) for _ in range(12)]
cases.append(('FSE weights', fse_header(lens8, 5, [0, -1, 5, 16, 10]) +
              codes_stream(lens8, msg), len(msg)))
# FSE-compressed weights, accuracy log 6, both states ending
lens6 = [1, 3, 3, 3, 4, 4]
msg = [0, 1, 5, 0, 2, 4, 3]
cases.append(('FSE weights, accuracy log 6',
              fse_header(lens6, 6, [0, 10, 39, -1, 14]) +
              codes_stream(lens6, msg), len(msg)))
# FSE table description with more than 12 repeat flags of 3 (zstd only)
counts = [0, 4, 4, 13, 10] + [0] * 43 + [-1]
cases.append(('FSE weights, long run of zeros',
              fse_header(lens8, 5, counts) + codes_stream(lens8, [3, 2, 1]),
              3))
# a description that zstd reads only by wrapping around (zstd only)
cases.append(('NCount wrapping around',
              bytes.fromhex('08700648e2eab2712a070d'), 6))
# from zstd's encoder
data = bytes(rng.choice(b'abcdefgh') for _ in range(30))
c = drive(['C 255 11 ' + data.hex()])[0]
assert c.startswith('OK '), c
cases.append(("zstd's encoder", bytes.fromhex(c[3:]), len(data)))

# literals in four streams, crafted and from zstd's encoder
def four_streams(hdr, lens, msg):
    q = (len(msg) + 3) // 4
    sts = [codes_stream(lens, g)
           for g in [msg[:q], msg[q:2*q], msg[2*q:3*q], msg[3*q:]]]
    return hdr + b''.join(bytes([len(t), 0]) for t in sts[:3]) + b''.join(sts)


lens2 = [1, 1]
cases4 = [('four streams, 7 bytes',
           four_streams(raw_header(lens2), lens2, [0, 1, 1, 0, 1, 0, 0]), 7),
          ('four streams, 3 bytes (RFC only)',
           four_streams(raw_header(lens2), lens2, [1, 0, 1]), 3),
          ('four streams, 12-bit codes',
           four_streams(raw_header(lens12), lens12,
                        [12, 11, 0, 5, 1, 0, 0, 3, 2]), 9),
          ('four streams, FSE weights',
           four_streams(fse_header(lens8, 5, [0, -1, 5, 16, 10]), lens8,
                        [rng.choice(range(8)) for _ in range(10)]), 10)]
data = bytes(rng.choice(b'abcdefgh') for _ in range(40))
c = drive(['E 255 11 ' + data.hex()])[0]
assert c.startswith('OK '), c
cases4.append(("four streams, zstd's encoder", bytes.fromhex(c[3:]),
               len(data)))


def ocaml_list(xs, indent='    '):
    lines, cur = [], '['
    for i, x in enumerate(xs):
        t = str(x) + ('; ' if i + 1 < len(xs) else '')
        if len(cur) + len(t) > 74:
            lines.append(cur.rstrip())
            cur = indent
        cur += t
    return '\n'.join(lines + [cur + ']'])


out = drive(['D %d %s' % (n, src.hex()) for _, src, n in cases])
print("""needs "tests/zstd/rfc8878_eval.ml";;

(* Generated by make_hol_tests.py: name, input, number of bytes and the      *)
(* output that zstd gives, with whether the RFC reading accepts the input.   *)

let hol_tests = [""")
items = []
for (name, src, n), o in zip(cases, out):
    assert o.startswith('OK'), (name, o)
    res = bytes.fromhex(o[3:])
    assert ref.huf_decompress1x1(True, src, n) == res, name
    try:
        rfc = ref.huf_decompress1x1(False, src, n) == res
    except ref.Fail:
        rfc = False
    items.append('  ("%s", %s,\n   %s,\n   %d,\n   %s)' % (
        name, 'true' if rfc else 'false', ocaml_list(src), n,
        ocaml_list(res)))
print(';\n'.join(items) + '];;')
print("""
let run_hol_test (name,rfc,bs,n,out) =
  let check zstd =
    let th = HUF_DECOMPRESS1X1_RULE zstd bs n in
    let expected = list_mk_icomb "huf_decompress1x1"
      [mk_bool zstd; mk_bytes bs; mk_bytes out] in
    aconv (concl th) expected && hyp th = [] in
  let ok = check true && (not rfc || check false) in
  Printf.printf "%-40s %s\\n%!" name (if ok then "OK" else "WRONG"); ok;;

let hol_tests_ok = forall (fun x -> run_hol_test x) hol_tests;;

(* Four streams: name, whether zstd and the RFC reading accept the input,    *)
(* the input, the number of bytes and the output.                            *)

let hol_tests4 = [""")
out4 = drive(['Q 32 %d %s' % (n, src.hex()) for _, src, n in cases4])
items = []
for (name, src, n), o in zip(cases4, out4):
    def mirror(zstd):
        try:
            return ref.huf_decompress4x1(zstd, src, n)
        except ref.Fail:
            return None
    dial, rfc = mirror(True), mirror(False)
    res = bytes.fromhex(o[3:]) if o.startswith('OK') else rfc
    assert res is not None and (o.startswith('OK') == (dial is not None)), name
    assert dial is None or dial == res, name
    assert rfc is None or rfc == res, name
    items.append('  ("%s", %s, %s,\n   %s,\n   %d,\n   %s)' % (
        name, 'true' if dial is not None else 'false',
        'true' if rfc is not None else 'false', ocaml_list(src), n,
        ocaml_list(res)))
print(';\n'.join(items) + '];;')
print("""
let run_hol_test4 (name,zok,rfc,bs,n,out) =
  let check zstd =
    let th = HUF_DECOMPRESS4X1_RULE zstd bs n in
    let expected = list_mk_icomb "huf_decompress4x1"
      [mk_bool zstd; mk_bytes bs; mk_bytes out] in
    aconv (concl th) expected && hyp th = [] in
  let ok = (not zok || check true) && (not rfc || check false) in
  Printf.printf "%-40s %s\\n%!" name (if ok then "OK" else "WRONG"); ok;;

let hol_tests4_ok = forall (fun x -> run_hol_test4 x) hol_tests4;;""")
