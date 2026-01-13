#!/bin/bash
# loventre_build_all_v9.sh
# Compilazione completa v9 nell’ordine corretto

set -e

echo ">>> Rimozione artefatti ..."
find . -name "*.vo" -delete -o -name "*.glob" -delete -o -name "*.vos" -delete -o -name "*.vok" -delete

echo ">>> 01 — CORE"
for f in \
  Loventre_Kernel \
  Loventre_Foundation_BaseTypes \
  Loventre_Foundation_Types \
  Loventre_Foundation_Params \
  Loventre_Foundation_Entropy \
  Loventre_Foundation_History_Structure \
  Loventre_Foundation_Time
do
  coqc -Q 01_Core Loventre_Core 01_Core/$f.v
done

echo ">>> 02 — ADVANCED + GEOMETRY"
for f in \
  Loventre_Curvature_Field \
  Loventre_Potential_Field \
  Loventre_Metrics_Bus \
  Geometry/Loventre_LMetrics_Structure
do
  coqc -Q 01_Core Loventre_Core -Q 02_Advanced Loventre_Advanced 02_Advanced/$f.v
done

echo ">>> 03 — MAIN v9"
for f in \
  Loventre_Main_Theorem_v9_Prelude \
  Loventre_LMetrics_v9_SAFE \
  Loventre_LMetrics_v9_Aliases \
  Loventre_LMetrics_v9_Risk \
  Loventre_GlobalDecision_Core \
  Loventre_GlobalDecision_View \
  Loventre_LMetrics_v9_Policy \
  Loventre_LMetrics_v9_MetaDecision \
  Loventre_LMetrics_v9_OneShot
do
  coqc -Q 01_Core Loventre_Core -Q 02_Advanced Loventre_Advanced -Q 03_Main Loventre_Main 03_Main/$f.v
done

echo ">>> 04 — TEST"
coqc -Q 01_Core Loventre_Core -Q 02_Advanced Loventre_Advanced -Q 03_Main Loventre_Main 03_Main/Loventre_Test_LMetrics_v9_All.v

echo ">>> 🎉 SUCCESSO: V9 COMPILATO COMPLETAMENTE!"

