#!/usr/bin/env bash
set -e

echo "===================================================="
echo " LOVENTRE ENGINE v7 — COMPILAZIONE Witness BASE"
echo "===================================================="

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
V7DIR="$ROOT/Coq_IO/LMetrics_v7"

echo "[INFO] Compilo LMetrics_v7_types.v"
coqc -Q "$V7DIR" LMetrics_v7 "$V7DIR/LMetrics_v7_types.v"

for f in "$V7DIR"/witness_json_m_v7_*.v; do
  echo ">> $f"
  coqc -Q "$V7DIR" LMetrics_v7 "$f"
done

echo "===================================================="
echo " 🎉 LMETRICS v7 CORE VERDE (Coq OK)"
echo "===================================================="

