#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

echo "[audit] checking tracked Coq build artifacts..."

bad_tracked="$(git ls-files | egrep '\.(vo|vos|vok|glob|aux)$' || true)"

if [ -n "$bad_tracked" ]; then
  echo "ERROR: trovati artefatti Coq TRACCIATI da git:"
  echo "$bad_tracked"
  exit 1
fi

echo "OK: nessun artefatto Coq tracciato"

