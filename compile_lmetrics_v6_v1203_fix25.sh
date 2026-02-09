#!/usr/bin/env bash
echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE v1203/fix25 3SAT (EH01)"
echo "===================================================="

cd ~/Library/Mobile\ Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed || exit 1

# Pulizia .vo/.vos
find Coq_IO/LMetrics_v6 -name "*.vo" -delete 2>/dev/null
find Coq_IO/LMetrics_v6 -name "*.vos" -delete 2>/dev/null
find Coq_IO/LMetrics_v6 -name "*.glob" -delete 2>/dev/null

echo "[INFO] Compila tipi v6 con namespace -Q"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v \
  || { echo "[ERRORE] types"; exit 1; }

echo "[INFO] Compila witness JSON con namespace -Q"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_json_m_v6_seed_01.v \
  || { echo "[ERRORE] seed_01"; exit 1; }

coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_json_m_v6_seed_02.v \
  || { echo "[ERRORE] seed_02"; exit 1; }

coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_json_m_v6_seed_03.v \
  || { echo "[ERRORE] seed_03"; exit 1; }

coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_json_m_v6_seed_04.v \
  || { echo "[ERRORE] seed_04"; exit 1; }

echo "===================================================="
echo " 🎉 VERDE v1203/fix25 — 3SAT easy & crit OK (EH01)"
echo "===================================================="

