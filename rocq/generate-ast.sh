#!/usr/bin/env bash
set -euo pipefail

# Generate AST JSON for every circuit file using the patched circom compiler.
#
# The patched compiler (--ast-json) writes a .json alongside each .circom file
# during the parse phase. We create a temporary driver that includes every
# circuit file, run the compiler, then collect the JSONs into ast/.

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CIRCOM="${CIRCOM:-$HOME/git/General/circom/target/release/circom}"

if [[ ! -x "$CIRCOM" ]]; then
  echo "error: circom binary not found at $CIRCOM" >&2
  echo "  Set \$CIRCOM or build the patched compiler." >&2
  exit 1
fi

cd "$REPO_ROOT"

# Clean output directory
rm -rf ast
mkdir -p ast

# Build a temporary driver that includes every .circom file in circuits/.
# Includes are relative to the -l search paths, so strip the circuits/ prefix.
DRIVER=$(mktemp "${TMPDIR:-/tmp}/ast-driver-XXXXXX.circom")
trap 'rm -f "$DRIVER"' EXIT

while IFS= read -r file; do
  rel="${file#circuits/}"
  echo "include \"$rel\";" >> "$DRIVER"
done < <(find circuits -name '*.circom' -type f | sort)

# Dummy main component — circom requires one, but we only need the parse phase.
# Use a template that's guaranteed to exist after the includes.
cat >> "$DRIVER" <<'EOF'

// Dummy main so circom doesn't refuse to start parsing.
// The --ast-json output is written during parsing, before main-component checks.
template __AstDriver() { signal input dummy; }
component main = __AstDriver();
EOF

echo "Running circom --ast-json ..."

# circom may exit non-zero because __AstDriver isn't meaningful, but the AST
# JSONs are already written by that point. We capture the exit code and only
# fail on truly unexpected errors (e.g. binary crash / signal).
set +e
"$CIRCOM" --ast-json -l circuits -l node_modules "$DRIVER" -o "${TMPDIR:-/tmp}" 2>&1
rc=$?
set -e

if [[ $rc -gt 1 ]]; then
  echo "warning: circom exited with code $rc (expected 0 or 1)" >&2
fi

# Collect JSONs from circuits/ into ast/, preserving directory structure.
echo "Collecting AST JSON files ..."
count=0
while IFS= read -r json; do
  rel="${json#circuits/}"
  dest="ast/$rel"
  mkdir -p "$(dirname "$dest")"
  mv "$json" "$dest"
  count=$((count + 1))
done < <(find circuits -name '*.json' -type f | sort)

echo "Collected $count JSON files into ast/"

# Clean up any JSONs that landed in node_modules/ (circomlib parses).
find node_modules -name '*.json.ast' -type f -delete 2>/dev/null || true
# The patched compiler writes .json (same base name, .circom -> .json)
# Remove only .json files that sit next to a .circom file in node_modules.
while IFS= read -r circom_file; do
  json_file="${circom_file%.circom}.json"
  [[ -f "$json_file" ]] && rm -f "$json_file"
done < <(find node_modules -name '*.circom' -type f 2>/dev/null)

echo "Done."
