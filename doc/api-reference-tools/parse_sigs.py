#!/usr/bin/env python3
import os as _os
_WD = _os.environ.get('APIDOC_WORKDIR', '/tmp')
"""Parse arm|x86/proofs/subroutine_signatures.ml into structured buffer roles.

Each entry:
 ("name",
   ([ (argname, ctype, "true"|"false"=is_const) ... ],
    "retty",
    [ (bufname, numelems, elembytes) ... ]   # input buffers
    [ ... ]                                   # output buffers
    [ ... ]                                   # temporary buffers
   ))
We extract name, arglist, ret, and the three buffer lists.
"""
import json, re, sys

def parse(path):
    txt = open(path, errors='replace').read()
    # remove (* ... *) comments (they don't nest here)
    txt = re.sub(r'\(\*.*?\*\)', '', txt, flags=re.S)
    out = {}
    # Split into top-level entries: ("name", ( ... ) ) ;
    # Find each entry start
    for m in re.finditer(r'\(\s*"([a-z0-9_]+)"\s*,', txt):
        name = m.group(1)
        # capture balanced parens from m.start()
        i = m.start()
        depth = 0
        j = i
        while j < len(txt):
            if txt[j] == '(':
                depth += 1
            elif txt[j] == ')':
                depth -= 1
                if depth == 0:
                    break
            j += 1
        entry = txt[i:j+1]
        rec = parse_entry(name, entry)
        if rec:
            out[name] = rec
    return out

def parse_string_triples(block):
    # matches ("a","b","c") or ("a","b",N)
    trips = re.findall(r'\(\s*"([^"]*)"\s*,\s*"([^"]*)"\s*,\s*"?([^",)]*)"?\s*\)', block)
    return trips

def bracket_lists(entry):
    # find all [...] top-level lists inside the entry
    lists = []
    depth = 0
    start = None
    for idx, ch in enumerate(entry):
        if ch == '[':
            if depth == 0:
                start = idx
            depth += 1
        elif ch == ']':
            depth -= 1
            if depth == 0:
                lists.append(entry[start:idx+1])
    return lists

def parse_entry(name, entry):
    lists = bracket_lists(entry)
    # Expected: [args], [inputs], [outputs], [temps]  (4 bracket lists)
    if len(lists) < 4:
        # some entries might have fewer if empty lists collapsed; pad
        while len(lists) < 4:
            lists.append('[]')
    args_l, in_l, out_l, tmp_l = lists[0], lists[1], lists[2], lists[3]
    args = parse_string_triples(args_l)   # (argname, ctype, isconst)
    def bufs(bl):
        return [(a,b,c) for a,b,c in parse_string_triples(bl)]
    # ret type: between the args list ']' and the '[' of inputs, there's ,"retty",
    after_args = entry[entry.find(args_l)+len(args_l):]
    rm = re.search(r'"\s*([A-Za-z0-9_ ]+?)\s*"', after_args)
    ret = rm.group(1) if rm else ''
    return {
        'args': [{'name':a,'ctype':b,'const':(c=='true')} for a,b,c in args],
        'ret': ret,
        'inputs': [{'name':a,'n':b,'elem':c} for a,b,c in bufs(in_l)],
        'outputs':[{'name':a,'n':b,'elem':c} for a,b,c in bufs(out_l)],
        'temps':  [{'name':a,'n':b,'elem':c} for a,b,c in bufs(tmp_l)],
    }

def main():
    res = {}
    for arch in ('arm','x86'):
        res[arch] = parse(f'{arch}/proofs/subroutine_signatures.ml')
    print(json.dumps(res, indent=1))

if __name__ == '__main__':
    main()
