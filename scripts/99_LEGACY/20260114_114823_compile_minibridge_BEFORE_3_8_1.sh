#!/usr/bin/env bash
set -e

echo "===================================================="
echo " LOVENTRE ENGINE v7 — COMPILAZIONE Mini-Bridge GENERAL"
echo "===================================================="

echo "[INFO] Pulizia artefatti"
rm -f Coq_IO/LMetrics_v7/*.vo Coq_IO/LMetrics_v7/*.glob Coq_IO/LMetrics_v7/*.vos Coq_IO/LMetrics_v7/*.vok 2>/dev/null || true

echo "[INFO] Compilo LMetrics_v7_Prelude.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 "Coq_IO/LMetrics_v7/LMetrics_v7_Prelude.v"

echo "[INFO] Compilo LMetrics_v7_types.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 "Coq_IO/LMetrics_v7/LMetrics_v7_types.v"

echo "[INFO] Compilo witness JSON v7 (produciamo .vo)"
for f in Coq_IO/LMetrics_v7/witness_json_m_v7_3sat_DIMACS_*.v; do
  echo ">> $f"
  coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 "$f"
done

echo "[INFO] Compilo LMetrics_v7_import.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 "Coq_IO/LMetrics_v7/LMetrics_v7_import.v"

echo "[INFO] Compilo LMetrics_v7_JSON_Index.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 "Coq_IO/LMetrics_v7/LMetrics_v7_JSON_Index.v"

echo "[INFO] Compilo LMetrics_v7_INDEX.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 "Coq_IO/LMetrics_v7/LMetrics_v7_INDEX.v"

echo "[INFO] Compilo LMetrics_v7_SELFTEST.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 "Coq_IO/LMetrics_v7/LMetrics_v7_SELFTEST.v"

echo "[INFO] Compilo LMetrics_v7_lemmas.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 "Coq_IO/LMetrics_v7/LMetrics_v7_lemmas.v"

echo "[INFO] Mini-bridge V7 completato"
echo "===================================================="
echo "[SUCCESS] Mini-Bridge GENERAL — STATO VERDE Coq"
echo "===================================================="

