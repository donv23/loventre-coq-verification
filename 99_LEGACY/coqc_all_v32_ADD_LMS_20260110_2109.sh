#!/bin/bash
set -e

echo "=== LOVENTRE V32 — FULL DEPENDENCY BUILD START ==="

####################################################
# 0) BUILD CANON v3 (stabile, indipendente)
####################################################
echo "[0] Build CANON v3 (coqc_all_v3.sh)"
bash coqc_all_v3.sh

####################################################
# 1) COMPILAZIONE STRATO JSON V32
####################################################

echo "[1] JSON V32 — Types"
coqc Loventre_v32_JSON_Types.v

echo "[2] JSON V32 — Loader (decodifica JSON → FlatLM)"
coqc Loventre_v32_JSON_Loader.v

echo "[3] JSON V32 — Conversione FlatLM → LMetrics"
coqc Loventre_v32_JSON_To_LMetrics.v

####################################################
# 2) WITNESS LOADER V32
####################################################

echo "[4] Witness Loader V32"
coqc Loventre_Witness_Loader.v

####################################################
# FINE
####################################################

echo "=== LOVENTRE V32 — BUILD OK ==="

