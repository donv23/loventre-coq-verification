#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
cd src

coqc Loventre_Geometric_Separation.v
coqc Loventre_Geometric_Separation_Corollary.v
coqc Loventre_Witness_Interpretation.v
coqc Loventre_Test_Geometric_Chain_Silent.v

echo "OK: src smoke chain (silent)"

