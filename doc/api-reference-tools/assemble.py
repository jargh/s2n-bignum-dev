#!/usr/bin/env python3
import os as _os
_WD = _os.environ.get('APIDOC_WORKDIR', '/tmp')
"""Assemble the final API_REFERENCE.md: front matter + body."""
import json

hdr_list = json.load(open(_os.path.join(_WD, 'hdr.json')))
names = sorted({r['name'] for r in hdr_list})

front = open(_os.path.join(_WD, 'front_matter.md')).read()
body  = open(_os.path.join(_WD, 'API_BODY.md')).read()

out = front.replace('<!-- BODY -->', body)
out = out.rstrip('\n') + '\n'   # exactly one trailing newline, no blank line at EOF
open(_os.path.join(_WD, 'API_REFERENCE.md'),'w').write(out)
print("assembled API_REFERENCE.md")
print("functions:", len(names))
