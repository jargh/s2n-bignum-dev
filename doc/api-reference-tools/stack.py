#!/usr/bin/env python3
"""Extract per-architecture stack-frame sizes (bytes below SP) from the
*_SUBROUTINE_CORRECT preconditions, writing $APIDOC_WORKDIR/stack.json."""
import os, json, re
WD = os.environ.get('APIDOC_WORKDIR', '/tmp')

specs = json.load(open(os.path.join(WD, 'specs.json')))
hdr = [r['name'] for r in json.load(open(os.path.join(WD, 'hdr.json')))]

def base(fn):
    for suf in ('_VARIABLE_TIME_arm','_VARIABLE_TIME_x86','_VARIABLE_TIME','_arm','_x86'):
        if fn.endswith(suf):
            return fn[:-len(suf)]
    return fn

def stk(fn, arch):
    k = base(fn).upper() + '_SUBROUTINE_CORRECT'
    pre = specs[arch].get(k)
    if pre is None:
        return None
    m = re.findall(r'word_sub stackpointer \(word (\d+)\)', pre)
    return max(int(x) for x in m) if m else 0

out = {fn: {'arm': stk(fn, 'arm'), 'x86': stk(fn, 'x86')} for fn in hdr}
json.dump(out, open(os.path.join(WD, 'stack.json'), 'w'))
print("wrote stack.json for", len(out), "functions")
