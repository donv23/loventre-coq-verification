#!/bin/bash
# ===========================================================
# LOVENTRE ENGINE v7 — Mini-Bridge Compile Script (General)
# Introduce explicit -Q binding for LMetrics_v7
# ===========================================================

set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

echo "===================================================="
echo " LOVENTRE ENGINE v7 — COMPILAZIONE Mini-Bridge GENERAL"
echo "===================================================="

echo "[INFO] Pulizia artefatti"
rm -f Coq_IO/LMetrics_v7/*.vo Coq_IO/LMetrics_v7/*.glob Coq_IO/LMetrics_v7/*.vok Coq_IO/LMetrics_v7/*.vos 2>/dev/null || true

COQCMD="coqc -Q Coq_IO/LMetrics_v7 ."

echo "[INFO] Compilo LMetrics_v7_Prelude.v"
$COQCMD Coq_IO/LMetrics_v7/LMetrics_v7_Prelude.v

echo "[INFO] Compilo LMetrics_v7_types.v"
$COQCMD Coq_IO/LMetrics_v7/LMetrics_v7_types.v

echo "[INFO] Compilo witness JSON v7"
for w in Coq_IO/LMetrics_v7/witness_json_*.v; do
  echo ">> $w"
  $COQCMD "$w"
done

echo "===================================================="
echo "[SUCCESS] Mini-Bridge v7 — STATO VERDE Coq"
echo "===================================================="

