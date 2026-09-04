#!/usr/bin/env python3
import os as _os
_WD = _os.environ.get('APIDOC_WORKDIR', '/tmp')
"""Extract the precondition (aliasing/assumption) block from every
*_SUBROUTINE_CORRECT theorem in arm/proofs and x86/proofs.

For each theorem we capture the text between the opening backtick of the
goal and the '==> ensures' marker. That block holds the nonoverlapping /
aligned / value-range preconditions that define the public contract.
Output: {arch: {theorem_name: precond_text}}.
"""
import json, re, glob, os

def extract(path):
    txt = open(path, errors='replace').read()
    out = {}
    # find each 'let NAME_SUBROUTINE_CORRECT = ... prove\n (`....`,'
    for m in re.finditer(r'let\s+([A-Za-z0-9_]*_SUBROUTINE_CORRECT)\s*=', txt):
        name = m.group(1)
        rest = txt[m.end():]
        # find first backtick that opens the goal
        bt = rest.find('`')
        if bt < 0:
            continue
        # goal ends at matching backtick; but there may be nested `...` in some.
        # We only need up to '==> ensures'. Find that within the goal region.
        # Grab a generous window then cut at '==> ensures'.
        window = rest[bt+1: bt+4000]
        idx = window.find('==> ensures')
        if idx < 0:
            # some specs use 'ensures arm' preceded by '==>' on prev line; fallback
            idx = window.find('ensures ')
        precond = window[:idx] if idx >= 0 else ''
        out[name] = ' '.join(precond.split())
    return out

def main():
    result = {}
    for arch in ('arm', 'x86'):
        d = {}
        for path in glob.glob(f'{arch}/proofs/*.ml'):
            d.update(extract(path))
        result[arch] = d
    print(json.dumps(result, indent=1))

if __name__ == '__main__':
    main()
