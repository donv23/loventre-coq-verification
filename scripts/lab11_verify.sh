#!/bin/zsh
set -euo pipefail

ROOT="/Users/vincenzoloventre/Desktop/loventre-coq-cycle11-lab"
cd "$ROOT"

echo "== LAB-11 VERIFY =="

echo "-- LAB-11.1 (Exclusivity)"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_11_Axiom_Breaking/L11_1_Exclusivity/Exclusivity_Core.v
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_11_Axiom_Breaking/L11_1_Exclusivity/CounterModel_Overlap.v

echo "-- LAB-11.2 (Irrev Hierarchy)"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_11_Axiom_Breaking/L11_2_IrrevHierarchy/IrrevHierarchy_Core.v
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_11_Axiom_Breaking/L11_2_IrrevHierarchy/CounterModel_EdgeNotPath.v

echo "OK: LAB-11 verification completed."

