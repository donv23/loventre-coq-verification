#!/bin/bash

# =============================================================
#  Loventre Coq Compile Wrapper v50
#  Regole auree:
#   - usa sempre questo script per compilare .v
#   - include i namespace nel giusto ordine
#   - esce con errore al primo KO
# =============================================================

set -e

coqc \
  -Q 01_Core Loventre_Core \
  -Q 02_Advanced Loventre_Advanced \
  -Q 03_Main Loventre_Main \
  -Q 04_JSON_Bridge_V50 Loventre_JSON \
  "$@"

