#!/usr/bin/env bash
# ============================================================
# Audit Axiom / Admitted — CANON
# Progetto: Loventre_Coq_Clean
# Scopo: garantire assenza di assiomi non dichiarati
# ============================================================

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="$ROOT/98_AUDIT"

mkdir -p "$OUT"

echo "=== AUDIT CANON — Axiom / Admitted ===" > "$OUT/audit_axioms_canon.txt"
echo "Data: $(date)" >> "$OUT/audit_axioms_canon.txt"
echo "" >> "$OUT/audit_axioms_canon.txt"

echo "--- Axiom ---" >> "$OUT/audit_axioms_canon.txt"
grep -R "^[[:space:]]*Axiom" \
  "$ROOT/01_Core" \
  "$ROOT/02_Advanced" \
  "$ROOT/03_Main" \
  >> "$OUT/audit_axioms_canon.txt" || true

echo "" >> "$OUT/audit_axioms_canon.txt"
echo "--- Admitted ---" >> "$OUT/audit_axioms_canon.txt"
grep -R "Admitted\." \
  "$ROOT/01_Core" \
  "$ROOT/02_Advanced" \
  "$ROOT/03_Main" \
  >> "$OUT/audit_axioms_canon.txt" || true

echo "" >> "$OUT/audit_axioms_canon.txt"
echo "=== FINE AUDIT ===" >> "$OUT/audit_axioms_canon.txt"

echo "[OK] Audit completato. Output in 98_AUDIT/audit_axioms_canon.txt"

