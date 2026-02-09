#!/bin/zsh
#
# ===============================================================
# LOVENTRE ENGINE v7 — Wrapper coqc trasparente
# ===============================================================
# Compila un file Coq con namespace minimo:
#   -Q Coq_IO/LMetrics_v7 LMetrics_v7
#
# Stampa il comando esatto che viene lanciato, così:
#   [RUNNING] coqc ... 02_Advanced/foo.v
#
# NESSUN fallback silenzioso.
# NESSUN trucco.
# ===============================================================

# Fail subito se il file non esiste
if [ ! -f "$1" ]; then
  echo "[ERROR] File non trovato: $1"
  exit 1
fi

# Costruiamo il comando reale
CMD="coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 \"$1\""

echo ""
echo "===================================================="
echo "[RUNNING] $CMD"
echo "===================================================="

# eseguiamo
eval $CMD

STATUS=$?

echo ""
if [ $STATUS -eq 0 ]; then
  echo "[OK] $1 compilato con successo"
else
  echo "[FAIL] Errore compilando $1 (exit $STATUS)"
fi

exit $STATUS

