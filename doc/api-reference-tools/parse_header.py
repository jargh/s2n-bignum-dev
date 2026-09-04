#!/usr/bin/env python3
import os as _os
_WD = _os.environ.get('APIDOC_WORKDIR', '/tmp')
"""Parse include/s2n-bignum.h into structured records.

A "comment block" is a maximal run of // lines. It applies to the run of
extern decls that immediately follow it (base + _alt siblings share one
comment). #ifdef __x86_64__ / #else / #endif select arch-specific prototypes.
"""
import json, re

HDR = "include/s2n-bignum.h"

def parse_extern(s):
    s = s.strip()
    m = re.match(r'extern\s+(.+?)\s+([A-Za-z_][A-Za-z0-9_]*)\s*\((.*)\)\s*;', s, re.S)
    if not m:
        return None
    ret, name, args = m.group(1), m.group(2), m.group(3)
    return {'name': name, 'ret': ret.strip(), 'args': ' '.join(args.split())}

def main():
    lines = open(HDR).read().splitlines()
    records = []
    i, n = 0, len(lines)
    cur_comment = []
    prev_was_comment = False
    arch_mode = 'both'
    buf = ''
    in_extern = False
    while i < n:
        stripped = lines[i].strip()

        if not in_extern and (stripped.startswith('#')):
            s = stripped
            if '__x86_64__' in s and (s.startswith('#if') or s.startswith('#ifdef')):
                arch_mode = 'x86'
            elif s.startswith('#else'):
                arch_mode = 'arm' if arch_mode == 'x86' else arch_mode
            elif s.startswith('#endif'):
                arch_mode = 'both'
            prev_was_comment = False
            i += 1
            continue

        if not in_extern and stripped.startswith('//'):
            if not prev_was_comment:
                cur_comment = []          # start a fresh block
            cur_comment.append(stripped[2:].strip())
            prev_was_comment = True
            i += 1
            continue

        if not in_extern and stripped == '':
            prev_was_comment = False       # blank ends a comment block run
            i += 1
            continue

        if stripped.startswith('extern') or in_extern:
            buf = (buf + ' ' + stripped).strip() if in_extern else stripped
            if ';' in stripped:
                in_extern = False
                rec = parse_extern(buf)
                if rec:
                    rec['desc'] = list(cur_comment)
                    rec['arch'] = arch_mode
                    records.append(rec)
                buf = ''
            else:
                in_extern = True
            prev_was_comment = False
            i += 1
            continue
        i += 1
    print(json.dumps(records, indent=1))

if __name__ == '__main__':
    main()
