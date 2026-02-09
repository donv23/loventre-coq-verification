#!/bin/bash

echo "===================================================="
echo " LOVENTRE ENGINE v7 — COMPILAZIONE Mini-Bridge GENERAL"
echo "===================================================="

# Pulizia artefatti
echo "[INFO] Pulizia artefatti"
rm -f Coq_IO/LMetrics_v7/*.vo Coq_IO/LMetrics_v7/*.glob Coq_IO/LMetrics_v7/*.vos Coq_IO/LMetrics_v7/*.vok

# Compilo base
echo "[INFO] Compilo LMetrics_v7_Prelude.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_Prelude.v || exit 1

echo "[INFO] Compilo LMetrics_v7_types.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_types.v || exit 1

# JSON witness loop
echo "[INFO] Compilo witness JSON v7 (produciamo .vo)"
for f in Coq_IO/LMetrics_v7/witness_json_m_v7_3sat_DIMACS_*.v; do
  echo ">> $f"
  coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 $f || exit 1
done

# Import
echo "[INFO] Compilo LMetrics_v7_import.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_import.v || exit 1

# JSON Index
echo "[INFO] Compilo LMetrics_v7_JSON_Index.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_JSON_Index.v || exit 1

# Index v7
echo "[INFO] Compilo LMetrics_v7_INDEX.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_INDEX.v || exit 1

# Selftest
echo "[INFO] Compilo LMetrics_v7_SELFTEST.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_SELFTEST.v || exit 1

# Lemmas
echo "[INFO] Compilo LMetrics_v7_lemmas.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_lemmas.v || exit 1

# safe/bh — deve venire prima del classify
echo "[INFO] Compilo LMetrics_v7_safe_bh.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_safe_bh.v || exit 1

# Classify
echo "[INFO] Compilo LMetrics_v7_classify.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_classify.v || exit 1

# Signature (nuovo stadio v7+)
echo "[INFO] Compilo LMetrics_v7_signature.v"
coqc -Q Coq_IO/LMetrics_v7 LMetrics_v7 Coq_IO/LMetrics_v7/LMetrics_v7_signature.v || exit 1

echo "[INFO] Mini-bridge V7 completato"
echo "===================================================="
echo "[SUCCESS] Mini-Bridge GENERAL — STATO VERDE Coq"
echo "===================================================="

