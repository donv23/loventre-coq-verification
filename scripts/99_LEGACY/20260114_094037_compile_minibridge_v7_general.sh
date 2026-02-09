#!/usr/bin/env bash
set -e

echo "===================================================="
echo " LOVENTRE ENGINE v7 — COMPILAZIONE Mini-Bridge GENERAL"
echo "===================================================="

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
COQDIR="$ROOT/Coq_IO/LMetrics_v7"
PATHOPT="-Q $COQDIR Coq_IO.LMetrics_v7"

echo "[INFO] Pulizia artefatti"
rm -f $COQDIR/*.vo $COQDIR/*.glob $COQDIR/*.vok $COQDIR/*.vos 2>/dev/null || true

echo "[INFO] Compilo LMetrics_v7_Prelude.v"
coqc $PATHOPT $COQDIR/LMetrics_v7_Prelude.v

echo "[INFO] Compilo LMetrics_v7_types.v"
coqc $PATHOPT $COQDIR/LMetrics_v7_types.v

echo "[INFO] Compilo witness JSON v7 (produciamo .vo)"
for W in $COQDIR/witness_json_m_v7_3sat_DIMACS_*.v; do
  echo ">> $W"
  coqc $PATHOPT "$W"
done

echo "[INFO] Compilo LMetrics_v7_import.v (ora i witness esistono)"
coqc $PATHOPT $COQDIR/LMetrics_v7_import.v

echo "===================================================="
echo "[SUCCESS] Mini-Bridge v7 — STATO VERDE Coq"
echo "===================================================="

