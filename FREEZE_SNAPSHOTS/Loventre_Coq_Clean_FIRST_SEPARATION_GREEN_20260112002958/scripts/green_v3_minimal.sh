#!/bin/zsh
set -e

cd "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/PROGETTO TEOREMA/Loventre_Coq_Modules/Loventre_Coq_Clean"

find . -name "*.vo"  -delete
find . -name "*.vos" -delete
find . -name "*.vok" -delete

coqc -Q 01_Core Loventre_Core 01_Core/Loventre_Core_Prelude.v

coqc -Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry 02_Advanced/Geometry/Loventre_Metrics_Bus.v
coqc -Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry 02_Advanced/Geometry/Loventre_LMetrics_Structure.v
coqc -Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry 02_Advanced/Geometry/Loventre_LMetrics_Phase_Predicates.v
coqc -Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry 02_Advanced/Geometry/Loventre_LMetrics_JSON_Witness.v
coqc -Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry 02_Advanced/Geometry/Loventre_LMetrics_Existence_Summary.v

coqc -Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry -Q 03_Main Loventre_Main 03_Main/Loventre_LMetrics_Policy_Specs.v
coqc -Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry -Q 03_Main Loventre_Main 03_Main/Loventre_LMetrics_Separation_Program.v
coqc -Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry -Q 03_Main Loventre_Main 03_Main/Loventre_Theorem_v3_P_vs_NP_like.v
coqc -Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry -Q 03_Main Loventre_Main 03_Main/Loventre_Theorem_v3_Citable_Prop.v
coqc -Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry -Q 03_Main Loventre_Main 03_Main/Test_Loventre_Theorem_v3_All.v

