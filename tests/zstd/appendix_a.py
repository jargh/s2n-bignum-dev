# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

# Check the mirror's FSE decoding tables (fse_table, following fse_spread,
# fse_nbits and fse_base) against Appendix A of RFC 8878, for the three
# predefined distributions of section 3.1.1.3.2.2. Erratum 6441 removes a
# first row "0 | 0 | 0 | 0" that each table has twice.
# usage: python3 -I appendix_a.py RFC8878_TXT
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rfc8878_ref as ref

txt = open(sys.argv[1]).read()


def dist(name):
    m = re.search(r'short ' + name + r'\[\d+\] =\s*\{([^}]*)\}', txt)
    return [int(x) for x in m.group(1).replace('\n', ' ').split(',')]


def appendix(title, nxt):
    start = txt.index('Appendix A.  Decoding Tables',
                      txt.index('Acknowledgments'))
    sec = txt[txt.index(title, start):]
    sec = sec[:sec.index(nxt)] if nxt else sec[:sec.index('Appendix B')]
    rows = re.findall(r'^\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|\s*(\d+)\s*\|'
                      r'\s*(\d+)\s*\|', sec, re.M)
    return [tuple(map(int, r)) for r in rows]


for name, alog, title, nxt in [
        ('literalsLength_defaultDistribution', 6,
         'A.1.  Literals Length Code Table', 'A.2.  Match Length Code Table'),
        ('matchLengths_defaultDistribution', 6,
         'A.2.  Match Length Code Table', 'A.3.  Offset Code Table'),
        ('offsetCodes_defaultDistribution', 5,
         'A.3.  Offset Code Table', None)]:
    cs = dist(name)
    rows = appendix(title, nxt)
    if rows and rows[0] == (0, 0, 0, 0) and rows[1][0] == 0:
        rows = rows[1:]                       # erratum 6441
    table = ref.fse_table(cs, alog)
    mine = [(u, s, nb, base) for u, (s, nb, base) in enumerate(table)]
    # Appendix A columns: State, Symbol, Number_Of_Bits, Base
    print(name, len(cs), 'symbols,', len(rows), 'rows,',
          'agree' if rows == mine else 'DIFFER')
    for a, b in zip(rows, mine):
        if a != b:
            print('   rfc', a, 'mirror', b)
            break
