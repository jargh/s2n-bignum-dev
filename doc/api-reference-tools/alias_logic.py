#!/usr/bin/env python3
import os as _os
_WD = _os.environ.get('APIDOC_WORKDIR', '/tmp')
r"""Derive a precise, per-function aliasing verdict from (a) the buffer roles in
subroutine_signatures and (b) the SUBROUTINE_CORRECT precondition text.

For each (output O, input I) pair we decide one of:
  INPLACE  : precond has "I = O \/ nonoverlapping(I..)(O..)"  -> may alias iff exactly equal
  DISJOINT : precond forces nonoverlapping(I,O) (directly, or via ALL/ALLPAIRS list
             containing both I and O) with NO in-place disjunction
  FREE     : precond never relates I and O -> arbitrary overlap allowed

Also detect: multiple output buffers mutual constraints, temp-buffer disjointness,
stack alignment requirement (aligned 16 stackpointer).

We then roll (O,I) verdicts up into one of a few human phrasings.
"""
import json, re

specs = json.load(open(_os.path.join(_WD, 'specs.json')))
sigs  = json.load(open(_os.path.join(_WD, 'sigs.json')))

def _base(fn):
    # ML-KEM/ML-DSA header names carry suffixes the proof theorem / signature
    # table drop: mldsa_ntt_arm -> MLDSA_NTT..., mlkem_rej_uniform_VARIABLE_TIME
    # -> MLKEM_REJ_UNIFORM...
    for suf in ('_VARIABLE_TIME_arm', '_VARIABLE_TIME_x86', '_VARIABLE_TIME', '_arm', '_x86'):
        if fn.endswith(suf):
            return fn[:-len(suf)]
    return fn

def key(fn): return _base(fn).upper()+'_SUBROUTINE_CORRECT'

def get_pre(fn, arch):
    pre = specs[arch].get(key(fn), '')
    if pre:
        return pre
    # try the other arch's dir under the base name (arch-only ML fns live in one dir)
    other = 'x86' if arch == 'arm' else 'arm'
    return specs[other].get(key(fn), '')

def get_sig_rec(fn, arch):
    return sigs[arch].get(fn) or sigs[arch].get(_base(fn)) \
        or sigs['arm'].get(fn) or sigs['x86'].get(fn) \
        or sigs['arm'].get(_base(fn)) or sigs['x86'].get(_base(fn))

def pair_verdict(pre, I, O):
    # in-place disjunction: "I = O \/ nonoverlapping" or "O = I \/ ..."
    # allow whitespace; names are simple idents
    inplace_pat = re.compile(r'\b%s\s*=\s*%s\s*\\/\s*nonoverlapping' % (re.escape(I), re.escape(O)))
    inplace_pat2= re.compile(r'\b%s\s*=\s*%s\s*\\/\s*nonoverlapping' % (re.escape(O), re.escape(I)))
    if inplace_pat.search(pre) or inplace_pat2.search(pre):
        return 'INPLACE'
    # hard nonoverlapping between I and O:
    #  a) direct "nonoverlapping (I,..) (O,..)" or reversed
    direct = re.compile(r'nonoverlapping[_a-z]*\s*\(\s*%s\b[^)]*\)\s*\(\s*%s\b' % (re.escape(I), re.escape(O)))
    direct2= re.compile(r'nonoverlapping[_a-z]*\s*\(\s*%s\b[^)]*\)\s*\(\s*%s\b' % (re.escape(O), re.escape(I)))
    if direct.search(pre) or direct2.search(pre):
        return 'DISJOINT'
    #  b) ALL (nonoverlapping (O,..)) [ ... (I,..) ... ]  -> O disjoint from list incl I
    #     find "ALL (nonoverlapping (O" then a bracket list mentioning I
    for mm in re.finditer(r'ALL\s*\(nonoverlapping\s*\(\s*([A-Za-z0-9_]+)\b', pre):
        anchor = mm.group(1)
        # the list follows; grab up to next ']'
        tail = pre[mm.end(): pre.find(']', mm.end())+1] if ']' in pre[mm.end():] else ''
        names_in_list = set(re.findall(r'\(\s*([A-Za-z0-9_]+)\b', tail))
        if anchor == O and I in names_in_list:
            return 'DISJOINT'
        if anchor == I and O in names_in_list:
            return 'DISJOINT'
    #  c) ALLPAIRS nonoverlapping [L1] [L2] with I in one and O in other, or both in the
    #     same "mutually disjoint" list
    for mm in re.finditer(r'ALLPAIRS\s+nonoverlapping\s*(\[[^\]]*\])\s*(\[[^\]]*\])?', pre):
        l1 = set(re.findall(r'\(\s*([A-Za-z0-9_]+)\b', mm.group(1)))
        l2 = set(re.findall(r'\(\s*([A-Za-z0-9_]+)\b', mm.group(2))) if mm.group(2) else set()
        if l2:
            if (I in l1 and O in l2) or (O in l1 and I in l2):
                return 'DISJOINT'
        else:
            if I in l1 and O in l1:
                return 'DISJOINT'
    return 'FREE'

def analyze(fn, arch):
    pre = get_pre(fn, arch)
    sig = get_sig_rec(fn, arch)
    if not pre or not sig:
        return None
    outs = [b['name'] for b in sig['outputs']]
    ins  = [b['name'] for b in sig['inputs']]
    temps= [b['name'] for b in sig['temps']]
    verds = {}
    for O in outs:
        for I in ins:
            verds[(O,I)] = pair_verdict(pre, I, O)
    return {
        'outs': outs, 'ins': ins, 'temps': temps,
        'verdicts': {f'{O}<-{I}': v for (O,I),v in verds.items()},
        'aligned16': 'aligned 16 stackpointer' in pre,
        'uses_stack': 'stackpointer' in pre,
        'raw': pre,
    }

if __name__ == '__main__':
    import sys
    hdr = json.load(open(_os.path.join(_WD, 'hdr.json')))
    want = sys.argv[1:] or ['bignum_add','bignum_mul','bignum_modinv','p256_montjadd',
                            'bignum_montmul_p256','bignum_mux','bignum_montifier','bignum_amontifier',
                            'curve25519_x25519','bignum_copy','bignum_optsub','bignum_sub']
    for fn in want:
        a = analyze(fn,'arm')
        print('=====',fn)
        if a:
            print('  verdicts:', a['verdicts'], '| aligned16=',a['aligned16'])
