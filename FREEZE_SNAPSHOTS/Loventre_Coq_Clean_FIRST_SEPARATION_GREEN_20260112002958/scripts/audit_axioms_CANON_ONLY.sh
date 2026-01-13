#!/usr/bin/env bash
# ============================================================
# Audit Axiom / Admitted — SOLO CANON COMPILANTE
# Esclude: 99_LEGACY, Geometry, .rtf, .save, sketch
# ============================================================

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/98_AUDIT"

mkdir -p "$OUT"

echo "=== AUDIT CANON COMPILANTE (NO LEGACY) ===" > "$OUT/audit_CANON_ONLY.txt"
echo "Data: $(date)" >> "$OUT/audit_CANON_ONLY.txt"
echo "" >> "$OUT/audit_CANON_ONLY.txt"

CANON_DIRS=(
  "$ROOT/01_Core"
  "$ROOT/02_Advanced"
  "$ROOT/03_Main"
)

FILTER_CMD='
  !/99_LEGACY/ &&
  !/Geometry/ &&
  /\.v$/ &&
  !/Sketch/ &&
  !/Seed/ &&
  !/Notes/ &&
  !/save/
'

echo "--- Axiom ---" >> "$OUT/audit_CANON_ONLY.txt"
grep -R "^[[:space:]]*Axiom" "${CANON_DIRS[@]}" | grep -E "$FILTER_CMD" \
  >> "$OUT/audit_CANON_ONLY.txt" || true

echo "" >> "$OUT/audit_CANON_ONLY.txt"
echo "--- Admitted ---" >> "$OUT/audit_CANON_ONLY.txt"
grep -R "Admitted\." "${CANON_DIRS[@]}" | grep -E "$FILTER_CMD" \
  >> "$OUT/audit_CANON_ONLY.txt" || true

echo "" >> "$OUT/audit_CANON_ONLY.txt"
echo "=== FINE AUDIT CANON ===" >> "$OUT/audit_CANON_ONLY.txt"

echo "[OK] Audit CANON completato. Output in 98_AUDIT/audit_CANON_ONLY.txt"

