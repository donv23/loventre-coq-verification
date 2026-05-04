#!/bin/zsh
set -euo pipefail

ROOT="/Users/vincenzoloventre/Desktop/loventre-coq-verification"
cd "$ROOT"

echo "== FREEZE VERIFY 2026-01 =="

echo "-- LAB-A1"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_A_Independence/A1_NoIrreversibility/Core_NoIrreversibility.v
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_A_Independence/A1_NoIrreversibility/CounterModel_Rigid.v

echo "-- LAB-A2"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_A_Independence/A2_NoTrichotomy/Core_NoTrichotomy.v
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_A_Independence/A2_NoTrichotomy/CounterModel_Tricho.v

echo "-- LAB-A3"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_A_Independence/A3_NoTerminality/Core_NoTerminality.v
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_A_Independence/A3_NoTerminality/CounterModel_Basin.v

echo "-- LAB-9"
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_9_AltFormalization/Alt_Core.v
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_9_AltFormalization/Alt_Bridge.v
coqc -Q 02_Advanced Loventre_Advanced \
  02_Advanced/LAB_9_AltFormalization/Alt_Rigidity.v

echo "-- SMOKE (CANON chain)"
make -f Makefile_SMOKE_ONLY verify

echo "-- AUDIT refresh"
mkdir -p 98_AUDIT
grep -RIn --exclude-dir=99_LEGACY --exclude-dir=99_ARCHIVE_V4_FREEZE --exclude-dir=98_AUDIT \
  -E "Axiom|Admitted|admit" 02_Advanced/LAB_A_Independence 02_Advanced/LAB_9_AltFormalization \
  > 98_AUDIT/LAB_FREEZE_AUDIT_2026-01.txt

echo "OK: freeze verification completed."

