#!/bin/zsh

echo "============================================"
echo " LOVENTRE ENGINE — batch_3sat_to_v6.sh"
echo " Converte tutti i CNF in JSON v6"
echo "============================================"

ROOT="$(dirname "$0")/.."
IN_DIR="$ROOT/3SAT_MINIBRIDGE/input_dimacs"
OUT_DIR="$ROOT/3SAT_MINIBRIDGE/json_out"

mkdir -p "$OUT_DIR"

echo "[INFO] Rimuovo eventuali JSON precedenti"
rm -f "$OUT_DIR"/m_v6_3sat_DIMACS_*.json

echo "[RUN] parse_3sat_to_json_v6.py"
"$ROOT/scripts/parse_3sat_to_json_v6.py"

echo "============================================"
echo " JSON generati in:"
echo "   $OUT_DIR"
echo "============================================"

