#!/bin/zsh
#
# Loventre Theorem v2 – Global Bridge Check
#
# Questo script esegue in sequenza:
#   1) Il test globale Coq v2 (Test_Loventre_Theorem_v2_All.v)
#   2) La regression suite Python del Loventre Engine
#   3) L'aggiornamento del profilo witness LMetrics
#   4) I controlli di Policy globale sui JSON metrics_*.json
#
# Obiettivo: verificare che il contratto Coq v2 (SAFE + Policy + Witness)
#            sia coerente con il motore Python reale (JSON + script).
#

set -e  # fail-fast: se un passo fallisce, lo script si ferma.

# Percorsi canone (dicembre 2025)
COQ_BIN="/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc"
COQ_ROOT="/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/PROGETTO TEOREMA/Loventre_Coq_Modules/Loventre_Coq_Clean"
PY_ROOT="/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"

echo "============================================================"
echo " Loventre – Theorem v2 Global Bridge Check"
echo "============================================================"
echo ""

echo "[1/4] Coq v2 – Test_Loventre_Theorem_v2_All.v"
echo "      Root Coq:  $COQ_ROOT"
echo "      Coq bin:   $COQ_BIN"
echo ""

cd "$COQ_ROOT"

"$COQ_BIN" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  -Q 03_Main           Loventre_Main \
  Test_Loventre_Theorem_v2_All.v

echo ""
echo "✔ Coq v2: Test_Loventre_Theorem_v2_All.v completato senza errori."
echo ""

echo "[2/4] Python – Regression suite Loventre Engine"
echo "      Root Python: $PY_ROOT"
echo ""

cd "$PY_ROOT"

python3 run_loventre_regression_suite.py

echo ""
echo "✔ Regression suite Python completata."
echo ""

echo "[3/4] Python – LMetrics Witness Profile (Markdown)"
echo ""

python3 loventre_lmetrics_witness_profile.py

echo ""
echo "✔ Aggiornato LOVENTRE_LMetrics_Witness_Profile.md."
echo ""

echo "[4/4] Python – Policy Spec Check sui metrics_*.json"
echo ""

python3 loventre_policy_spec_check.py

echo ""
echo "✔ Policy spec check completato."
echo ""

echo "============================================================"
echo " Loventre – Theorem v2 Global Bridge Check: TUTTO OK ✅"
echo "============================================================"
echo ""

