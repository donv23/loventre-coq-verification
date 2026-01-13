#!/bin/zsh
set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

echo "== LOVENTRE: Guardiano Citabile v3 =="
echo "Root: $ROOT"
echo ""

COMMON_ARGS="-Q 01_Core Loventre_Core -Q 02_Advanced/Geometry Loventre_Geometry -Q 03_Main Loventre_Main"

echo "== Debug coqc (ambiente interattivo) =="
zsh -ic 'whence -v coqc || true; command -v coqc || true; type coqc || true; coqc -v || true'
echo ""

echo "== Step 1: Citable One Command =="
zsh -ic "cd \"$ROOT\" && coqc $COMMON_ARGS 03_Main/Loventre_Citable_One_Command_v3.v"

echo ""
echo "== Step 2: Test_Loventre_Theorem_v3_All =="
zsh -ic "cd \"$ROOT\" && coqc $COMMON_ARGS 03_Main/Test_Loventre_Theorem_v3_All.v"

echo ""
echo "OK: Guardiano Citabile v3 completato."

