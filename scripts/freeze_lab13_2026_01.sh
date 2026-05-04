#!/usr/bin/env bash
set -euo pipefail

cd /Users/vincenzoloventre/Desktop/loventre-coq-cycle11-lab

echo "== FREEZE LAB-13 =="

./scripts/lab13_verify.sh

echo "-- AUDIT REFRESH --"
mkdir -p 98_AUDIT
grep -RIn --exclude-dir=99_LEGACY --exclude-dir=98_AUDIT \
  -E "Axiom|Admitted|admit" 02_Advanced/LAB_13_Global_Rigidity \
  > 98_AUDIT/LAB13_AUDIT_2026-01.txt

echo "OK: LAB-13 frozen"

