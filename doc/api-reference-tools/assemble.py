#!/usr/bin/env python3
import os as _os
_WD = _os.environ.get('APIDOC_WORKDIR', '/tmp')
"""Assemble the final API_REFERENCE.md: front matter + A-Z index + body."""
import json, re

hdr_list = json.load(open(_os.path.join(_WD, 'hdr.json')))
names = sorted({r['name'] for r in hdr_list})

# GitHub-style anchor from a heading '### `name`': strip backticks, lowercase,
# spaces->hyphens, drop other punctuation. Our names are [a-z0-9_], but a few
# carry uppercase (VARIABLE_TIME), which GitHub lowercases in the slug.
def anchor(n):
    return n.lower()

# Build a compact alphabetical index grouped by leading token for scanability,
# but as one flat list of links (per user: strictly flat A-Z). We render it as a
# wrapped list of code-links separated by mid-dots.
links = [f"[`{n}`](#{anchor(n)})" for n in names]
# chunk into lines of ~6 for readability
index_lines = []
row = []
for l in links:
    row.append(l)
    if len(row) == 6:
        index_lines.append(' · '.join(row)); row = []
if row: index_lines.append(' · '.join(row))
# Use a trailing <br> for the hard line break rather than two trailing spaces,
# so the file carries no trailing whitespace (keeps whitespace-checkers/hooks happy).
index_md = '<br>\n'.join(index_lines)

front = open(_os.path.join(_WD, 'front_matter.md')).read()
body  = open(_os.path.join(_WD, 'API_BODY.md')).read()

out = front.replace('<!-- INDEX -->', index_md).replace('<!-- BODY -->', body)
out = out.rstrip('\n') + '\n'   # exactly one trailing newline, no blank line at EOF
open(_os.path.join(_WD, 'API_REFERENCE.md'),'w').write(out)
print("assembled API_REFERENCE.md")
print("functions:", len(names))
