#!/bin/bash
# =========================================================
# LOVENTRE ENGINE v7 — wrapper di compilazione Coq
# con gestione corretta dei namespace v7 e dei witness
# =========================================================

set -e

FILE="$1"

if [ -z "$FILE" ]; then
  echo "[ERRORE] Nessun file .v specificato."
  exit 1
fi

echo ""
echo "===================================================="
echo "[RUNNING] coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 \"$FILE\""
echo "===================================================="

# Aggiungiamo anche la current directory al SEARCH PATH
# così Coq vede i .vo compilati con LMetrics_v7_import
coqc \
  -Q Coq_IO/LMetrics_v7 LMetrics_v7 \
  -R Coq_IO/LMetrics_v7 LMetrics_v7 \
  "$FILE"

echo ""
echo "[OK] $FILE compilato con successo"
echo ""

