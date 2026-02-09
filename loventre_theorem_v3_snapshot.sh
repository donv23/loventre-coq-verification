#!/usr/bin/env bash
# ============================================================
# Loventre – Theorem v3 Snapshot (Coq v2 + Python v3)
# ============================================================
# Scopo:
#   - Eseguire il bridge check v2 completo (Coq + Python).
#   - Mostrare il riepilogo dei witness principali v3 (m_P, m_Pacc, m_NP_*).
#   - Rigenerare il file Coq auto-generato con i Definition m_* : LMetrics.
#
# Nota:
#   - Questo script NON modifica alcun file dentro Loventre_Coq_Clean.
#   - Si limita a chiamare:
#       ./loventre_theorem_v2_bridge_check.sh
#       python3 loventre_v3_main_witness_summary.py
#       python3 loventre_v3_main_witness_coq_export.py
# ============================================================

set -euo pipefail

ENGINE_ROOT="$(cd "$(dirname "$0")" && pwd)"

echo "============================================================"
echo " Loventre – Theorem v3 Snapshot (Coq v2 + Python v3)"
echo "============================================================"
echo "Root motore: ${ENGINE_ROOT}"
echo ""

# ------------------------------------------------------------
# [1] Bridge v2 completo (Coq + Python)
# ------------------------------------------------------------
echo "[1/3] Bridge v2 – check completo (Coq + Python)"
echo "------------------------------------------------------------"
if [ -x "${ENGINE_ROOT}/loventre_theorem_v2_bridge_check.sh" ]; then
  "${ENGINE_ROOT}/loventre_theorem_v2_bridge_check.sh"
else
  echo "[ERRORE] Script loventre_theorem_v2_bridge_check.sh non trovato o non eseguibile."
  echo "         Assicurati che esista in:"
  echo "         ${ENGINE_ROOT}"
fi
echo ""

# ------------------------------------------------------------
# [2] Riepilogo witness v3 (Python)
# ------------------------------------------------------------
echo "[2/3] Witness v3 – riepilogo principale (Python)"
echo "------------------------------------------------------------"
python3 "${ENGINE_ROOT}/loventre_v3_main_witness_summary.py" || {
  echo "[ERRORE] loventre_v3_main_witness_summary.py non è andato a buon fine."
}
echo ""

# ------------------------------------------------------------
# [3] Export Coq delle definizioni m_* : LMetrics
# ------------------------------------------------------------
echo "[3/3] Export Coq – LOVENTRE_V3_Main_Witness_From_JSON.v"
echo "------------------------------------------------------------"
python3 "${ENGINE_ROOT}/loventre_v3_main_witness_coq_export.py" || {
  echo "[ERRORE] loventre_v3_main_witness_coq_export.py non è andato a buon fine."
}
echo ""

echo "============================================================"
echo " Loventre – Theorem v3 Snapshot COMPLETATO"
echo "============================================================"
echo ""
echo "Ora puoi, se vuoi:"
echo "  - controllare i log del bridge v2,"
echo "  - rileggere la tabella di riepilogo v3,"
echo "  - aprire il file auto-generato:"
echo "      LOVENTRE_V3_Main_Witness_From_JSON.v"
echo "    per copiare gli snippet dentro Loventre_Coq_Clean."
echo ""

