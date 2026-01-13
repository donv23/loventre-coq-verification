#!/bin/bash
# loventre_freeze_v9.sh
# Congela lo stato del sorgente Coq v9 in una snapshot timestamped
# Regole Auree rispettate: zero editing manuale

set -e

TS=$(date +"%Y-%m-%d_%H-%M-%S")
FREEZE_DIR="FREEZE/LOVENTRE_COQ_v9_$TS"

echo ">>> Creazione cartella freeze: $FREEZE_DIR"
mkdir -p "$FREEZE_DIR"

echo ">>> Copio 01_Core ..."
cp -R 01_Core "$FREEZE_DIR/"

echo ">>> Copio 02_Advanced ..."
cp -R 02_Advanced "$FREEZE_DIR/"

echo ">>> Copio 03_Main ..."
cp -R 03_Main "$FREEZE_DIR/"

echo ">>> Copio scripts ..."
cp -R scripts "$FREEZE_DIR/"

echo ">>> Copio README/seed se presenti ..."
cp -f README.md "$FREEZE_DIR/" 2>/dev/null || true
cp -f *seed* "$FREEZE_DIR/" 2>/dev/null || true

echo ">>> ZIP opzionale"
zip -r "$FREEZE_DIR.zip" "$FREEZE_DIR" >/dev/null 2>&1 || true

echo ">>> FREEZE COMPLETATO!"
echo "     Percorso: $FREEZE_DIR"
echo "     (e zip se riuscito)"

