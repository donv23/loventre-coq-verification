#!/bin/bash
set -e

echo "=== LOVENTRE V32 — FULL DEPENDENCY BUILD START ==="

echo "[0] Build CANON v3 (coqc_all_v3.sh)"
bash coqc_all_v3.sh

echo "[A] Compiling LMetrics (CANON file used by V32)"
coqc Loventre_LMetrics_Structure.v

echo "[1] JSON V32 — Types"
coqc Loventre_v32_JSON_Types.v

echo "[2] JSON V32 — Loader (decodifica JSON → FlatLM)"
coqc Loventre_v32_JSON_Loader.v

echo "[3] JSON V32 — Conversione FlatLM → LMetrics"
coqc Loventre_v32_JSON_To_LMetrics.v

echo "[4] JSON V32 — Witness Loader"
coqc Loventre_Witness_Loader.v

echo "[✔] LOVENTRE V32 — BUILD OK"

