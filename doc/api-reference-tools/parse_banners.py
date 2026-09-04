#!/usr/bin/env python3
import os as _os
_WD = _os.environ.get('APIDOC_WORKDIR', '/tmp')
"""Extract the descriptive banner from every arm/*.S and x86/*.S (excluding
tutorial/ and proofs/). The banner is the first '// ----' delimited comment
block. We split into:
  - summary:  the leading line(s) before the blank that ends the header-style
              "Inputs .../output ..." preamble
  - prose:    the remaining descriptive paragraphs (prototype + ABI removed)
  - abi:      the ABI mapping line(s)
"""
import json, os, re, glob

RULE = re.compile(r'^//\s*-{10,}\s*$')

def clean(l):
    return re.sub(r'^//\s?', '', l).rstrip()

def extract_banner(path):
    lines = open(path, errors='replace').read().splitlines()
    idx = [i for i, l in enumerate(lines) if RULE.match(l)]
    if len(idx) < 2:
        return None
    body = [clean(l) for l in lines[idx[0]+1: idx[1]]]

    prose, abi = [], []
    i = 0
    n = len(body)
    while i < n:
        ls = body[i].strip()
        # ABI line(s)
        if 'ABI:' in ls or re.match(r'^(Standard|Microsoft)\b.*ABI', ls):
            abi.append(body[i]); i += 1; continue
        # prototype block: a line that starts a C decl, consume through ';'
        if re.match(r'^(extern\b|static\b)', ls) or re.match(r'^(void|uint\d+_t|int\d+_t|size_t)\s+[A-Za-z_]\w*\s*\(', ls):
            # consume until a line containing ';'
            while i < n and ';' not in body[i]:
                i += 1
            if i < n:
                i += 1  # skip the line with ';'
            continue
        prose.append(body[i]); i += 1

    # collapse: trim leading/trailing blank prose lines
    while prose and prose[0].strip() == '': prose.pop(0)
    while prose and prose[-1].strip() == '': prose.pop()
    return {'prose': prose, 'abi': abi}

def main():
    out = {}
    for arch in ('arm', 'x86'):
        for path in glob.glob(f'{arch}/*/*.S'):
            if '/tutorial/' in path or '/proofs/' in path:
                continue
            name = os.path.basename(path)[:-2]
            ban = extract_banner(path) or {'prose': [], 'abi': [], 'missing': True}
            ban['path'] = path
            out.setdefault(name, {})[arch] = ban
    print(json.dumps(out, indent=1))

if __name__ == '__main__':
    main()
