#!/bin/sh
# Regenerate doc/API_REFERENCE.md from the in-repo sources of truth.
# Run from the repository root:  sh doc/api-reference-tools/build.sh
set -e

TOOLS=doc/api-reference-tools
WD="${APIDOC_WORKDIR:-$TOOLS/.work}"
export APIDOC_WORKDIR="$WD"
mkdir -p "$WD"

if [ ! -f include/s2n-bignum.h ]; then
  echo "error: run from the repository root (include/s2n-bignum.h not found)" >&2
  exit 1
fi

# Static inputs the generator loads from the work dir.
cp "$TOOLS/front_matter.md" "$WD/front_matter.md"
cp "$TOOLS/alias_logic.py"  "$WD/alias_logic.py"

# 1. Parsers (emit JSON on stdout -> capture into the work dir).
python3 "$TOOLS/parse_header.py"  > "$WD/hdr.json"
python3 "$TOOLS/parse_banners.py" > "$WD/banners.json"
python3 "$TOOLS/parse_sigs.py"    > "$WD/sigs.json"
python3 "$TOOLS/parse_specs.py"   > "$WD/specs.json"

# 2. Derived data (write their own JSON into the work dir).
python3 "$TOOLS/assumptions.py"
python3 "$TOOLS/stack.py"
python3 "$TOOLS/deltas.py"

# 3. Generate the per-function body and assemble the final document.
python3 "$TOOLS/gen_final.py"
python3 "$TOOLS/assemble.py"

cp "$WD/API_REFERENCE.md" doc/API_REFERENCE.md
echo "wrote doc/API_REFERENCE.md"
