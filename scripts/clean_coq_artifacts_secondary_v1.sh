#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

echo "[clean] removing Coq build artifacts (.vo/.vos/.vok/.glob) ..."
find 04_Classical_Bridge -type f \( -name "*.vo" -o -name "*.vos" -o -name "*.vok" -o -name "*.glob" \) -print -delete 2>/dev/null || true
echo "[clean] done"

