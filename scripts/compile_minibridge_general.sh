#!/bin/zsh
echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE Mini-Bridge GENERAL"
echo "===================================================="

cd $(dirname $0)/..

echo "[INFO] Pulizia artefatti"
find Coq_IO/LMetrics_v6 -name "*.vo"   -delete
find Coq_IO/LMetrics_v6 -name "*.glob" -delete

echo "[INFO] Compilo LMetrics_v6_types.v (tipi di base)"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 \
     Coq_IO/LMetrics_v6/LMetrics_v6_types.v || exit 1

echo "[INFO] Compilo witness derivati"
for f in Coq_IO/LMetrics_v6/witness_json_m_v6_seed_*.v; do
  echo ">> $f"
  coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 $f  || exit 1
done

echo "[INFO] Compilo modulo generale"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 \
     Coq_IO/LMetrics_v6/Loventre_Minibridge_General.v || exit 1

echo "[INFO] Compilo modulo test"
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 \
     Coq_IO/LMetrics_v6/Loventre_Minibridge_General_Test.v || exit 1

echo "===================================================="
echo " 🎉 GENERAL Mini-Bridge VERDE (Coq OK)"
echo "===================================================="

