#!/bin/zsh
set -e
setopt nullglob  # zsh: ignora glob senza match

echo "===================================================="
echo " LOVENTRE ENGINE v7 — COMPILAZIONE Mini-Bridge GENERAL"
echo "===================================================="

ROOT="$HOME/Desktop/ALGORITIMIA_BACKUP/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"
COQDIR="$ROOT/Coq_IO/LMetrics_v7"
COQC="$ROOT/scripts/coqc_v7.sh"

cd "$ROOT"

echo "[INFO] Pulizia artefatti"
rm -f $COQDIR/*.vo $COQDIR/*.glob \
      $COQDIR/*.vok $COQDIR/*.vos

echo "[INFO] Compilo LMetrics_v7_Prelude.v"
$COQC $COQDIR/LMetrics_v7_Prelude.v

echo "[INFO] Compilo LMetrics_v7_types.v"
$COQC $COQDIR/LMetrics_v7_types.v

echo "[INFO] Compilo witness JSON v7 (produciamo .vo)"
for f in $COQDIR/witness_json_m_v7_3sat_DIMACS_*.v; do
  echo ">> $f"
  $COQC "$f"
done

echo "[INFO] Compilo LMetrics_v7_import.v"
$COQC $COQDIR/LMetrics_v7_import.v

echo "[INFO] Mini-bridge V7 completato"
echo "===================================================="
echo "[SUCCESS] Mini-Bridge GENERAL — STATO VERDE Coq"
echo "===================================================="

