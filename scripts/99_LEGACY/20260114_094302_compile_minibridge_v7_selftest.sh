#!/bin/bash

echo "===================================================="
echo " LOVENTRE ENGINE v7 — COMPILAZIONE SELFTEST         "
echo "===================================================="

set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

cd "$ROOT"

echo "[INFO] Uso lo stesso layout del bridge GENERAL"
COQC="coqc -q -R Coq_IO LMetrics_v7"

echo "[INFO] Compilo SELFTEST"
$COQC Coq_IO/LMetrics_v7/LMetrics_v7_SELFTEST.v

echo
echo "===================================================="
echo " [SUCCESS] SELFTEST v7 — STATO VERDE Coq"
echo "===================================================="

