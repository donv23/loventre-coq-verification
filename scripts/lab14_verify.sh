#!/bin/zsh
set -e

cd /Users/vincenzoloventre/Desktop/loventre-coq-cycle11-lab

echo "== LAB-14 VERIFY =="
echo "-- LAB-14.1 (Core Partial Path Rigidity)"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_14_Partial_Rigidity/L14_1_Core/Core_Partial_Path_Rigidity.v

echo "-- LAB-14.2 (CounterModel Partial Path Rigidity)"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_14_Partial_Rigidity/L14_2_CounterModel/CounterModel_Partial_Path_Rigidity.v

echo "OK: LAB-14 verification completed."

