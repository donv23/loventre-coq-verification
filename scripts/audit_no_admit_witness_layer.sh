#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

files=(
  "src/Loventre_Witness_Interpretation.v"
  "src/Loventre_Test_Geometric_Chain_Silent.v"
)

echo "[audit] checking no 'admit/Admitted' in witness layer & silent chain..."

for f in "${files[@]}"; do
  if [ ! -f "$f" ]; then
    echo "ERROR: file mancante: $f"
    exit 1
  fi

  if egrep -n '\bAdmitted\b|\badmit\b' "$f" >/dev/null 2>&1; then
    echo "ERROR: trovati admit/Admitted in $f"
    egrep -n '\bAdmitted\b|\badmit\b' "$f" || true
    exit 1
  fi

  echo "OK: $f (no admit/Admitted)"
done

echo "OK: witness layer clean (no admit/Admitted)"

