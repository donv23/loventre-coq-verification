#!/bin/zsh

echo "===================================================="
echo " LOVENTRE ENGINE — COMPILAZIONE Mini-Bridge 3SAT"
echo "===================================================="

ROOT="$(dirname "$0")/.."
COQ_DIR="$ROOT/Coq_IO/LMetrics_v6"
JSON_DIR="$ROOT/3SAT_MINIBRIDGE/json_out"
COQ_OUT="$ROOT/3SAT_MINIBRIDGE/coq_out"

mkdir -p "$COQ_OUT"

echo "[INFO] Pulizia Coq artefatti"
find "$COQ_DIR" -name "*.vo"   -delete
find "$COQ_DIR" -name "*.vos"  -delete
find "$COQ_DIR" -name "*.glob" -delete

echo "[INFO] Genero witness da JSON"
"$ROOT/scripts/loventre_json_to_v6.py"

echo "[INFO] Compilo file LMetrics_v6_types.v"
coqc -Q "$COQ_DIR" LMetrics_v6 "$COQ_DIR"/LMetrics_v6_types.v || {
    echo "[ERRORE] Non riesco a compilare LMetrics_v6_types.v"
    exit 1
}

echo "[INFO] Compilo witness generati"
for f in "$COQ_DIR"/witness_json_m_v6_seed_*.v; do
    echo ">> $f"
    coqc -Q "$COQ_DIR" LMetrics_v6 "$f" || {
        echo "[ERRORE] Fallito su $f"
        exit 1
    }
done

echo "===================================================="
echo " 🎉 Mini-Bridge 3SAT VERDE (Coq OK)"
echo "===================================================="

