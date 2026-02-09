#!/bin/zsh

set -e
ROOT=$(dirname $0)/..

echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE Giudice Mini-Bridge "
echo "===================================================="

cd $ROOT

# Compila il tipo
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v

# Compila il giudice
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/Loventre_Minibridge_Judge.v

# Compila i witness
for W in Coq_IO/LMetrics_v6/witness_json_m_v6_seed_*.v; do
  echo ">> $W"
  coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 $W
done

# Compila il test finale
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/Loventre_Minibridge_Test.v

echo "===================================================="
echo " 🎉 GIUDICE Mini-Bridge VERDE (Coq OK)"
echo "===================================================="

