#!/bin/zsh

echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE v1204/fix26 SOFTFLAG"
echo "===================================================="
cd ~/Library/Mobile\ Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed

find Coq_IO/LMetrics_v6 -name "*.vo"   -delete
find Coq_IO/LMetrics_v6 -name "*.glob" -delete

echo "[INFO] Compila tipi LMetrics v6"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v || exit 1

echo "[INFO] Compila witness JSON v6"
for f in Coq_IO/LMetrics_v6/witness_json_m_v6_seed_*.v; do
  echo ">> $f"
  coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 "$f" || exit 1
done

echo "===================================================="
echo " 🎉 VERDE v1204/fix26 — SOFTFLAG ABILITATO"
echo "===================================================="

