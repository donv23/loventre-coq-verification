#!/bin/bash
##
## LOVENTRE ENGINE — TAB LEGGERA v1200/fix22
## Compila LMetrics_v6_types e witness 000–063
##

ROOT="$HOME/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"

echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE v1200/fix22 FULL GRID"
echo " Target: types + minimal + 001–063"
echo "===================================================="

if [ ! -d "$ROOT" ]; then
  echo "[ERRORE] Root non trovata: $ROOT"
  exit 1
fi

cd "$ROOT"

echo "[INFO] Pulizia artefatti Coq"
find . -type f \( -name "*.vo" -o -name "*.vos" -o -name "*.glob" -o -name "*.vok" -o -name "*.vio" \) -delete

echo "[INFO] Compilazione sequenziale"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v \
|| { echo "[ERRORE] types FALLITO"; exit 1; }

for F in Coq_IO/LMetrics_v6/witness_v6_*.v; do
  echo ">> coqc $F"
  coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 $F || {
    echo "[ERRORE] Fallito su $F"
    exit 2
  }
done

echo "===================================================="
echo " 🎉 VERDE v1200/fix22 FULL GRID"
echo "   - TUTTI i witness 000–063 OK"
echo "===================================================="
exit 0

