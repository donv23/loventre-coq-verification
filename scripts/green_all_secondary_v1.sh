#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

echo "[green] Secondary_Tab: cleaning Coq artifacts..."
./scripts/clean_coq_artifacts_secondary_v1.sh

echo "[green] compiling Axis C Public Weak base module..."
./scripts/coqc_axis_c 04_Classical_Bridge/Loventre_Axis_C_Public_Weak.v

echo "[green] compiling Axis C Public Weak entrypoint..."
./scripts/coqc_axis_c 04_Classical_Bridge/Loventre_Axis_C_Public_Weak_Index.v

echo "[green] compiling consumer test..."
./scripts/coqc_axis_c 04_Classical_Bridge/Loventre_Axis_C_Public_Weak_Consumer_Test.v

echo "[green] compiling safety test..."
./scripts/coqc_axis_c 04_Classical_Bridge/Test_Public_Weak_Safety.v

echo "OK: green_all_secondary_v1 (Axis C Public Weak compiles)"

