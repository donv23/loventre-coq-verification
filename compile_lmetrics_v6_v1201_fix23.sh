#!/bin/bash
##
## LOVENTRE ENGINE — v1201/fix23
## FULL GRID + JSON Witness
## 
## Regole auree:
## - compilazione sequenziale
## - nessuna cancellazione di file canonici
## - arresto immediato su errore
##

ROOT="$HOME/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"

echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE v1201/fix23"
echo " Target: types + v6_000–063 + JSON"
echo "===================================================="

if [ ! -d "$ROOT" ]; then
  echo "[ERRORE] Root non trovata:"
  echo "  $ROOT"
  exit 1
fi

cd "$ROOT" || exit 1

echo "[INFO] Pulizia artefatti Coq"
find . -type f \( -name "*.vo" -o -name "*.glob" -o -name "*.vos" -o -name "*.vok" -o -name "*.vio" \) -delete

echo "[INFO] Compila tipi"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v \
|| { echo "[ERRORE] LMetrics_v6_types FALLITO"; exit 2; }

echo "[INFO] Compila witness canonici"
for F in Coq_IO/LMetrics_v6/witness_v6_*.v; do
  echo ">> $F"
  coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 "$F" \
  || { echo "[ERRORE] Fallito su $F"; exit 3; }
done

echo "[INFO] Compila witness JSON"
for F in Coq_IO/LMetrics_v6/witness_json_*.v; do
  echo ">> $F"
  coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 "$F" \
  || { echo "[ERRORE] Fallito su $F"; exit 4; }
done

echo "===================================================="
echo " 🎉 VERDE v1201/fix23 FULL + JSON"
echo "===================================================="
exit 0

