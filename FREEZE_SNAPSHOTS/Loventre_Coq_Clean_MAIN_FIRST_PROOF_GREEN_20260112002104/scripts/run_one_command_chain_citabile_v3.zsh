#!/bin/zsh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

echo "== LOVENTRE: One-Command Chain (Citabile v3) =="

GUARD="$ROOT/scripts/run_guardiano_citabile_v3.zsh"
if [[ ! -f "$GUARD" ]]; then
  echo "ERRORE: guardiano non trovato:"
  echo "$GUARD"
  exit 1
fi

OUT_FILE="$(mktemp -t loventre_onecmd_citabile_v3.XXXXXX)"
cleanup () { rm -f "$OUT_FILE" 2>/dev/null || true; }
trap cleanup EXIT

# Esegue il guardiano stampando a schermo + catturando output per estrarre il Log:
zsh "$GUARD" | tee "$OUT_FILE"

LOG_PATH="$(grep -m1 '^Log: ' "$OUT_FILE" | sed 's/^Log: //')"
if [[ -n "${LOG_PATH}" ]]; then
  echo ""
  echo "== LOG (guardiano citabile v3) =="
  echo "${LOG_PATH}"
fi

