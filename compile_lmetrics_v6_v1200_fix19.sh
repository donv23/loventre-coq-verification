#!/bin/bash
##
## LOVENTRE ENGINE — TAB LEGGERA v1200/fix19-EH01
## Script minimale per costruire LMetrics_v6_types e witness_v6_minimal
## Solo namespace LMetrics_v6 — senza import di 01_Core/02_Advanced/03_Main
##
ROOT="$HOME/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"

echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE v1200/fix19-EH01"
echo " Solo LMetrics_v6"
echo "===================================================="

if [ ! -d "$ROOT" ]; then
  echo "[ERRORE] Root non trovata: $ROOT"
  exit 1
fi

cd "$ROOT"

echo "[INFO] Pulizia artefatti Coq"
find . -type f \( -name "*.vo" -o -name "*.vos" -o -name "*.glob" -o -name "*.vok" -o -name "*.vio" \) -delete

echo "[INFO] Verifica file target"
if [ ! -f "Coq_IO/LMetrics_v6/LMetrics_v6_types.v" ]; then
  echo "[ERRORE] Mancante: Coq_IO/LMetrics_v6/LMetrics_v6_types.v"
  exit 2
fi

if [ ! -f "Coq_IO/LMetrics_v6/witness_v6_minimal.v" ]; then
  echo "[ERRORE] Mancante: Coq_IO/LMetrics_v6/witness_v6_minimal.v"
  exit 3
fi

echo "[INFO] Compilazione LMetrics_v6_types.v"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 \
     Coq_IO/LMetrics_v6/LMetrics_v6_types.v
if [ $? -ne 0 ]; then
  echo "[ERRORE] Compilazione LMetrics_v6_types FALLITA"
  exit 4
fi

echo "[INFO] Compilazione witness_v6_minimal.v"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 \
     Coq_IO/LMetrics_v6/witness_v6_minimal.v
if [ $? -ne 0 ]; then
  echo "[ERRORE] witness_v6_minimal FALLITO"
  exit 5
fi

echo "===================================================="
echo " 🎉 VERDE: BUILD LMetrics_v6 completato"
echo "   - LMetrics_v6_types.vo"
echo "   - witness_v6_minimal.vo"
echo "===================================================="
exit 0

