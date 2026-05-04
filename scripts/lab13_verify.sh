#!/usr/bin/env bash
set -euo pipefail

echo "== LAB-13 VERIFY =="

echo "-- LAB-13.1 (Core Global Path)"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_13_Global_Rigidity/L13_1_Core/Core_Global_Path.v

echo "-- LAB-13.2 (CounterModel Global Path)"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_13_Global_Rigidity/L13_2_CounterModel/CounterModel_Global_Path.v

echo "-- LAB-13.3 (Core Global Acyclic)"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_13_Global_Rigidity/L13_3_Acyclic/Core/Core_Global_Acyclic.v

echo "-- LAB-13.3 (CounterModel Global Acyclic)"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_13_Global_Rigidity/L13_3_Acyclic/CounterModel/CounterModel_Global_Acyclic.v

echo "OK: LAB-13 verification completed."

