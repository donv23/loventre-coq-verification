#!/bin/zsh

# Vai alla root del progetto Loventre Engine
cd ~/Library/"Mobile Documents"/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed || exit 1

# Pulisci artefatti Coq nella cartella LMetrics_v6
rm -f Coq_IO/LMetrics_v6/*.vos Coq_IO/LMetrics_v6/*.vok Coq_IO/LMetrics_v6/*.glob Coq_IO/LMetrics_v6/*.vio

# Compila LMetrics_v6_types.v
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v || { echo "Errore compiling types"; exit 2 }

# Compila il witness minimale
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_v6_minimal.v || { echo "Errore compiling witness"; exit 3 }

# Controlla i .vo generati
ls -l Coq_IO/LMetrics_v6/*.vo

