#!/usr/bin/env bash
set -e

cd ~/Library/Mobile\ Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed

echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE v1206/fix28 FINAL"
echo "===================================================="

echo "[INFO] Compila tipi"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v

echo "[INFO] Compila witness JSON FINAL"
for f in Coq_IO/LMetrics_v6/witness_json_m_v6_seed_*.v; do
  echo ">> $f"
  coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 "$f"
done

echo "===================================================="
echo " 🎉 VERDE v1206/fix28 — COMPLETO"
echo "===================================================="

