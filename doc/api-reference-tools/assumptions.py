#!/usr/bin/env python3
import os as _os
_WD = _os.environ.get('APIDOC_WORKDIR', '/tmp')
"""Extract clean structural/value-range preconditions per function from the
SUBROUTINE_CORRECT specs. Returns a list of human-readable assumption strings.
Only keep 'clean' conjuncts (no embedded comments, quantifiers, or memory reads)."""
import json, re

specs = json.load(open(_os.path.join(_WD, 'specs.json')))

def clean_conjuncts(pre):
    if not pre: return []
    # cut everything after first quantifier-with-memory or comment marker
    out=[]
    for c in pre.split('/\\'):
        c=' '.join(c.split())
        if not c: continue
        if c.startswith('!'):  # leading forall of the goal — strip var list up to '.'
            c=c.split('.',1)[1].strip() if '.' in c else ''
        if not c: continue
        # skip noise
        if any(t in c for t in ['nonoverlapping','aligned 16 stackpointer','ALL ','ALL(',
                                'ALLPAIRS','adrp','word_sub stackpointer','//','memory :>',
                                'read ','C_ARGUMENTS','ensures','bignum_from_memory','!i.',
                                'aligned_bytes_loaded','MAYCHANGE','LENGTH','inlist','wordlist']):
            continue
        # keep only genuine arithmetic preconds
        if re.search(r'\b(val|ODD|EVEN|divides|LENGTH)\b', c) or re.search(r'[<>]=?|EXP|MOD', c):
            # translate a bit
            t = translate(c)
            if t: out.append(t)
    # dedupe preserve order
    seen=set(); res=[]
    for x in out:
        if x not in seen: seen.add(x); res.append(x)
    return res

def translate(c):
    s=c
    s=s.replace('2 EXP ','2^')
    s=re.sub(r'\bval\s+([a-z0-9_]+)', r'\1', s)
    s=s.replace('ODD n','n (the modulus) is odd')
    s=re.sub(r'\bODD\s+([a-z0-9_]+)', r'\1 is odd', s)
    s=re.sub(r'([0-9]+) divides ([a-z0-9_]+)', r'\2 is a multiple of \1', s)
    s=s.strip()
    # filter obviously-internal names
    if s in ('T','F'): return None
    return s

def main():
    hdr=[r['name'] for r in json.load(open(_os.path.join(_WD, 'hdr.json')))]
    def base(fn):
        for suf in ('_VARIABLE_TIME_arm','_VARIABLE_TIME_x86','_VARIABLE_TIME','_arm','_x86'):
            if fn.endswith(suf): return fn[:-len(suf)]
        return fn
    res={}
    for fn in hdr:
        k=base(fn).upper()+'_SUBROUTINE_CORRECT'
        pre=specs['arm'].get(k) or specs['x86'].get(k) or ''
        cs=clean_conjuncts(pre)
        if cs: res[fn]=cs
    json.dump(res, open(_os.path.join(_WD, 'assumptions.json'),'w'), indent=1)
    print("wrote assumptions.json for", len(res), "functions")

if __name__=='__main__':
    main()
