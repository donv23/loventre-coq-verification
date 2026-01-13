#!/usr/bin/env bash
# ============================================================
# Audit Axiom / Admitted — SOLO FILE REALMENTE COMPILATI
# (filtra wildcard e token non-path)
# ============================================================

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/98_AUDIT"
MAKEFILE="$ROOT/Makefile_SMOKE_ONLY"

mkdir -p "$OUT"

OUTFILE="$OUT/audit_CANON_FROM_MAKEFILE.txt"

echo "=== AUDIT CANON (FILE DA MAKEFILE_SMOKE_ONLY) ===" > "$OUTFILE"
echo "Data: $(date)" >> "$OUTFILE"
echo "" >> "$OUTFILE"

# Estrae solo path che finiscono in .v e contengono /
FILES=$(grep -oE '[A-Za-z0-9_./-]+\.v' "$MAKEFILE" \
        | grep '/' \
        | sort -u)

echo "--- FILE ANALIZZATI ---" >> "$OUTFILE"
for f in $FILES; do
  echo "$f" >> "$OUTFILE"
done

echo "" >> "$OUTFILE"
echo "--- Axiom ---" >> "$OUTFILE"
for f in $FILES; do
  grep "^[[:space:]]*Axiom" "$ROOT/$f" >> "$OUTFILE" || true
done

echo "" >> "$OUTFILE"
echo "--- Admitted ---" >> "$OUTFILE"
for f in $FILES; do
  grep "Admitted\." "$ROOT/$f" >> "$OUTFILE" || true
done

echo "" >> "$OUTFILE"
echo "=== FINE AUDIT CANON ===" >> "$OUTFILE"

echo "[OK] Audit CANON da Makefile completato."
echo "     Output in 98_AUDIT/audit_CANON_FROM_MAKEFILE.txt"

