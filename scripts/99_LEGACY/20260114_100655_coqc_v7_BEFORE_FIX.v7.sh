#!/bin/zsh
set -e
setopt nullglob

ROOT="$HOME/Desktop/ALGORITIMIA_BACKUP/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"

exec coqc \
  -Q "$ROOT/Coq_IO/LMetrics_v7" LMetrics_v7 \
  "$@"

