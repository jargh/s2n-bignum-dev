#!/usr/bin/env python3
"""Compute per-public-function architecture availability, writing
$APIDOC_WORKDIR/deltas.json. Availability is determined from which arch
directories actually define the symbol (S2N_BN_SYMBOL / visibility directive),
so it stays accurate as x86 ML-KEM/ML-DSA support lands."""
import os, json, glob, re
from collections import defaultdict
WD = os.environ.get('APIDOC_WORKDIR', '/tmp')

hdr = json.load(open(os.path.join(WD, 'hdr.json')))
ban = json.load(open(os.path.join(WD, 'banners.json')))
sigs = json.load(open(os.path.join(WD, 'sigs.json')))

def arch_symbols():
    present = defaultdict(set)
    for arch in ('arm', 'x86'):
        for path in glob.glob(f'{arch}/*/*.S'):
            if '/tutorial/' in path or '/proofs/' in path:
                continue
            txt = open(path, errors='replace').read()
            for m in re.finditer(r'S2N_BN_SYMBOL\(([A-Za-z0-9_]+)\)', txt):
                present[m.group(1)].add(arch)
            for m in re.finditer(r'S2N_BN_SYM_VISIBILITY_DIRECTIVE\(([A-Za-z0-9_]+)\)', txt):
                present[m.group(1)].add(arch)
    return present

present = arch_symbols()

def norm(t):
    return re.sub(r'\bstatic\b', '', t).replace(' ', '')

def argsig(s):
    return [(a['name'], norm(a['ctype'])) for a in s['args']] if s else None

def norm_prose(p):
    return [l.rstrip() for l in p if l.strip() != '']

records = {}
for r in hdr:
    records.setdefault(r['name'], r)

out = {}
for fn, rec in records.items():
    arches = present.get(fn, set())
    avail = set(a for a in ('arm', 'x86') if a in arches)
    if not avail:
        avail = {'arm', 'x86'} if rec['arch'] == 'both' else {rec['arch']}
    ba = ban.get(fn, {})
    parm = norm_prose(ba.get('arm', {}).get('prose', [])) if 'arm' in ba else None
    px86 = norm_prose(ba.get('x86', {}).get('prose', [])) if 'x86' in ba else None
    prose_differ = (parm is not None and px86 is not None and parm != px86)
    sa, sx = sigs['arm'].get(fn), sigs['x86'].get(fn)
    sig_differ = bool(sa and sx and argsig(sa) != argsig(sx))
    out[fn] = {'avail': sorted(avail), 'hdr_arch': rec['arch'],
               'prose_differ': prose_differ, 'sig_differ': sig_differ}

json.dump(out, open(os.path.join(WD, 'deltas.json'), 'w'), indent=1)
print("wrote deltas.json for", len(out), "functions")
