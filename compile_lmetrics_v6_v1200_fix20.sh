#!/bin/bash
##
## LOVENTRE ENGINE — TAB LEGGERA v1200/fix20
## Compila:
##   - LMetrics_v6_types.v
##   - witness_v6_minimal.v
##   - witness_v6_001.v
##
## Conforme alle regole auree (Gennaio 2026)
##

ROOT="$HOME/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"

echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE v1200/fix20"
echo " Target: types + minimal + 001"
echo "===================================================="

if [ ! -d "$ROOT" ]; then
  echo "[ERRORE] Root non trovata: $ROOT"
  exit 1
fi

cd "$ROOT"

echo "[INFO] Pulizia artefatti Coq"
find . -type f \( -name "*.vo" -o -name "*.vos" -o -name "*.glob" -o -name "*.vok" -o -name "*.vio" \) -delete

echo "[INFO] Verifica file target"
for F in \
  Coq_IO/LMetrics_v6/LMetrics_v6_types.v \
  Coq_IO/LMetrics_v6/witness_v6_minimal.v \
  Coq_IO/LMetrics_v6/witness_v6_001.v
do
  if [ ! -f "$F" ]; then
    echo "[ERRORE] Mancante file: $F"
    exit 2
  fi
done

echo "[INFO] Compilazione LMetrics_v6_types.v"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 \
     Coq_IO/LMetrics_v6/LMetrics_v6_types.v \
 || { echo "[ERRORE] types FALLITO"; exit 3; }

echo "[INFO] Compilazione witness_v6_minimal.v"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 \
     Coq_IO/LMetrics_v6/witness_v6_minimal.v \
 || { echo "[ERRORE] minimal FALLITO"; exit 4; }

echo "[INFO] Compilazione witness_v6_001.v"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 \
     Coq_IO/LMetrics_v6/witness_v6_001.v \
 || { echo "[ERRORE] witness_001 FALLITO"; exit 5; }

echo "===================================================="
echo " 🎉 VERDE v1200/fix20"
echo "   - LMetrics_v6_types.vo"
echo "   - witness_v6_minimal.vo"
echo "   - witness_v6_001.vo"
echo "===================================================="
exit 0

