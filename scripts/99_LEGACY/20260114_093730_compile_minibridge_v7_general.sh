#!/bin/bash
set -e

echo "===================================================="
echo " LOVENTRE ENGINE v7 — COMPILAZIONE Mini-Bridge GENERAL"
echo "===================================================="

echo "[INFO] Pulizia artefatti"
rm -f Coq_IO/LMetrics_v7/*.vo Coq_IO/LMetrics_v7/*.glob \
      Coq_IO/LMetrics_v7/*.vok Coq_IO/LMetrics_v7/*.vos || true

echo "[INFO] Compilo LMetrics_v7_Prelude.v"
coqc Coq_IO/LMetrics_v7/LMetrics_v7_Prelude.v

echo "[INFO] Compilo LMetrics_v7_types.v"
coqc Coq_IO/LMetrics_v7/LMetrics_v7_types.v

echo "[INFO] Compilo witness JSON v7 (produciamo .vo)"
for f in Coq_IO/LMetrics_v7/witness_json_m_v7_3sat_DIMACS_*.v; do
  echo ">> $f"
  coqc "$f"
done

echo "[INFO] Compilo LMetrics_v7_lemmas.v"
coqc Coq_IO/LMetrics_v7/LMetrics_v7_lemmas.v

echo "[INFO] Compilo LMetrics_v7_import.v (ora i witness esistono)"
coqc Coq_IO/LMetrics_v7/LMetrics_v7_import.v

echo "===================================================="
echo "[SUCCESS] Mini-Bridge v7 — STATO VERDE Coq"
echo "===================================================="

