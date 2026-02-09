#!/bin/bash
set -e

echo "=== LOVENTRE COQ v3 — CANONICAL BUILD START ==="

# Pulizia artefatti locali (NON cancella sorgenti)
rm -f *.vo *.vos *.vok *.glob

echo "[1/7] Compiling core class layer"
coqc Loventre_v3_LClass.v

echo "[2/7] Compiling curvature layer"
coqc Loventre_v3_Curvature.v

echo "[3/7] Compiling delta-curvature layer"
coqc Loventre_v3_DeltaCurvature.v

echo "[4/7] Compiling asymmetry layer"
coqc Loventre_v3_Asymmetry.v

echo "[5/7] Compiling final theorem layer"
coqc Loventre_v3_Final.v

echo "[6/7] Compiling JSON bridge"
coqc Loventre_v3_JSON_Bridge.v

echo "[7/7] Re-check curvature (stability test)"
coqc Loventre_v3_Curvature.v

echo "=== LOVENTRE COQ v3 — BUILD OK (GREEN) ==="

