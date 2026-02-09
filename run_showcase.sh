#!/bin/zsh

# Script di comodo per lanciare il Loventre Three Regimes Showcase
# Uso:
#   ./run_showcase.sh              -> usa esempio_history.json
#   ./run_showcase.sh history.json -> usa il file passato come argomento

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

HISTORY_FILE="${1:-esempio_history.json}"

python3 "$SCRIPT_DIR/loventre_three_regimes_showcase.py" \
        "$SCRIPT_DIR/$HISTORY_FILE"

