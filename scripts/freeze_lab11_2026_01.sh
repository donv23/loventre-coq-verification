#!/usr/bin/env bash
set -e

echo "== FREEZE LAB-11 =="
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_11_Axiom_Breaking/L11_1_Exclusivity/Exclusivity_Core.v
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_11_Axiom_Breaking/L11_1_Exclusivity/CounterModel_Overlap.v

coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_11_Axiom_Breaking/L11_2_IrrevHierarchy/IrrevHierarchy_Core.v
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_11_Axiom_Breaking/L11_2_IrrevHierarchy/CounterModel_EdgeNotPath.v

./scripts/lab11_verify.sh
echo "OK: LAB-11 frozen"

