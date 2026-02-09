#!/bin/zsh
set -e
setopt nullglob

echo "===================================================="
echo " LOVENTRE ENGINE v7 — COMPILAZIONE SELFTEST         "
echo "===================================================="

ROOT="$HOME/Desktop/ALGORITIMIA_BACKUP/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"
COQDIR="$ROOT/Coq_IO/LMetrics_v7"
COQC="$ROOT/scripts/coqc_v7.sh"

cd "$ROOT"

echo "[INFO] Pulizia artefatti"
rm -f $COQDIR/*.vo $COQDIR/*.glob $COQDIR/*.vok $COQDIR/*.vos

echo "[INFO] Compilo Prelude e Types"
$COQC $COQDIR/LMetrics_v7_Prelude.v
$COQC $COQDIR/LMetrics_v7_types.v

echo "[INFO] Compilo witness JSON v7"
for f in $COQDIR/witness_json_m_v7_3sat_DIMACS_*.v; do
  echo ">> $f"
  $COQC "$f"
done

echo "[INFO] Compilo Import"
$COQC $COQDIR/LMetrics_v7_import.v

echo "[INFO] Compilo SELFTEST FINALE"
$COQC $COQDIR/LMetrics_v7_SELFTEST.v

echo "===================================================="
echo "[SUCCESS] SELFTEST v7 — STATO VERDE Coq"
echo "===================================================="

