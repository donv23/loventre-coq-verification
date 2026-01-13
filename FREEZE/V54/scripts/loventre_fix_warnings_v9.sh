#!/bin/bash
# loventre_fix_warnings_v9.sh
# Patch automatica v9 — rimuove warning:
#  1. "From Coq" → "From Stdlib"
#  2. app_length → length_app
# Regole auree rispettate: zero modifiche manuali

set -e

echo ">>> Patching From Coq → From Stdlib ..."
find 01_Core 02_Advanced 03_Main \
  -name "*.v" \
  -exec sed -i '' 's/From Coq/From Stdlib/g' {} +

echo ">>> Patching app_length → length_app ..."
find 01_Core \
  -name "*.v" \
  -exec sed -i '' 's/app_length/length_app/g' {} +

echo ">>> Completato! Ora ricompila."

