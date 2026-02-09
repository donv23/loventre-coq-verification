#!/bin/bash
##
## LOVENTRE ENGINE — v1202/fix24 SAFE Layer
## Full grid + SAFE-aware JSON reconstruction
##

ROOT="$HOME/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"

echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE v1202/fix24 SAFE"
echo "===================================================="

if [ ! -d "$ROOT" ]; then
  echo "[ERRORE] Root non trovata: $ROOT"
  exit 1
fi

cd "$ROOT" || exit 1

echo "[INFO] Pulizia artefatti Coq"
find . -type f \( -name "*.vo" -o -name "*.glob" -o -name "*.vos" -o -name "*.vok" -o -name "*.vio" \) -delete

echo "[INFO] Compila tipi"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v \
|| { echo "[ERRORE] types FAIL"; exit 2; }

echo "[INFO] Compila witness canonici"
for F in Coq_IO/LMetrics_v6/witness_v6_*.v; do
  coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 "$F" \
  || { echo "[ERRORE] FAIL su $F"; exit 3; }
done

echo "[INFO] Compila witness JSON SAFE-aware"
for F in Coq_IO/LMetrics_v6/witness_json_*.v; do
  coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 "$F" \
  || { echo "[ERRORE] FAIL su $F"; exit 4; }
done

echo "===================================================="
echo " 🎉 VERDE v1202/fix24 SAFE COMPLETO"
echo "===================================================="
exit 0

