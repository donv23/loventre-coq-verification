#!/bin/zsh
# ============================================================
# LOVENTRE PROJECT – FREEZE LAB-12 (Minimal Rigidity)
# Date: 2026-01
# ============================================================

echo "== FREEZE LAB-12 =="
cd /Users/vincenzoloventre/Desktop/loventre-coq-cycle11-lab || exit 1

echo "-- LAB-12 VERIFY =="
# Verifica compilazione di tutti i file LAB-12
coqc -Q 02_Advanced Loventre_Advanced 02_Advanced/LAB_12_Minimal_Rigidity/L12_1_MinCore/Core_Minimal.v
coqc -Q 02_Advanced Loventre_Advanced 02_Advanced/LAB_12_Minimal_Rigidity/L12_1_MinCore/CounterModel_NoGlobalRigidity.v
coqc -Q 02_Advanced Loventre_Advanced 02_Advanced/LAB_12_Minimal_Rigidity/L12_2_Pairwise/Core_Pairwise.v
coqc -Q 02_Advanced Loventre_Advanced 02_Advanced/LAB_12_Minimal_Rigidity/L12_2_Pairwise/CounterModel_Pairwise.v
coqc -Q 02_Advanced Loventre_Advanced 02_Advanced/LAB_12_Minimal_Rigidity/L12_3_Triplet/Core_Triplet.v
coqc -Q 02_Advanced Loventre_Advanced 02_Advanced/LAB_12_Minimal_Rigidity/L12_3_Triplet/CounterModel_Triplet.v

echo "-- AUDIT REFRESH --"
mkdir -p 98_AUDIT
grep -RIn --exclude-dir=99_LEGACY --exclude-dir=98_AUDIT \
  -E "Axiom|Admitted|admit" 02_Advanced/LAB_12_Minimal_Rigidity \
  > 98_AUDIT/LAB12_AUDIT_2026-01.txt

echo "OK: LAB-12 verification + freeze completed."
# ============================================================

