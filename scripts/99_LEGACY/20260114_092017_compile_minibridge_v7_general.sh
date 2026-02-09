#!/bin/zsh
echo "===================================================="
echo " LOVENTRE ENGINE v7 — COMPILAZIONE Mini-Bridge GENERAL"
echo "===================================================="

# 1. Pulizia
echo "[INFO] Pulizia artefatti"
rm -f Coq_IO/LMetrics_v7/*.vo Coq_IO/LMetrics_v7/*.vos Coq_IO/LMetrics_v7/*.vok Coq_IO/LMetrics_v7/*.glob

# 2. Compila prelude e types con namespace corretto
echo "[INFO] Compilo LMetrics_v7_Prelude.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_Prelude.v || exit 1

echo "[INFO] Compilo LMetrics_v7_types.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_types.v || exit 1

# 3. Compila tutti i witness JSON
echo "[INFO] Compilo witness JSON v7"
for F in Coq_IO/LMetrics_v7/witness_json_m_v7_*.v; do
  echo ">> $F"
  coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 "$F" || exit 1
done

echo "[OK] BUILD COMPLETATA"

