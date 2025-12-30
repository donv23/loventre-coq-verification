#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

files=(
  "src/Loventre_Witness_Interpretation.v"
  "src/Loventre_Test_Geometric_Chain_Silent.v"
)

echo "[audit] checking no real 'admit./Admitted.' in witness layer & silent chain..."

# Cerchiamo SOLO comandi/tattiche reali:
#   - "Admitted." come comando di chiusura prova
#   - "admit." / "Admit." come tattica, anche dopo bullet "- "
# Questo evita falsi positivi in commenti tipo "Nessun Admitted."
pattern='^[[:space:]]*([-+*][[:space:]]*)?(admit\.|Admit\.|Admitted\.)'

for f in "${files[@]}"; do
  if [ ! -f "$f" ]; then
    echo "ERROR: file mancante: $f"
    exit 1
  fi

  if grep -nE "$pattern" "$f" >/dev/null 2>&1; then
    echo "ERROR: trovati admit./Admitted. REALI in $f"
    grep -nE "$pattern" "$f" || true
    exit 1
  fi

  echo "OK: $f (no admit./Admitted.)"
done

echo "OK: witness layer clean (no admit./Admitted.)"

