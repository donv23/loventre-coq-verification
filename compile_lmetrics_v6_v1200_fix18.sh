#!/bin/zsh

# --- Vai alla root del progetto Loventre Engine ---
cd ~/Library/"Mobile Documents"/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed || exit 1

# --- Disabilita errori glob ---
setopt nullglob

# --- Pulizia artefatti Coq ---
rm -f Coq_IO/LMetrics_v6/*.vos Coq_IO/LMetrics_v6/*.vok Coq_IO/LMetrics_v6/*.glob Coq_IO/LMetrics_v6/*.vio

# --- Compila types file con namespace ---
echo "Compilazione LMetrics_v6_types.v..."
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v || { echo "Errore compiling types"; exit 2 }

# --- Crea il witness minimale corretto ---
cat > Coq_IO/LMetrics_v6/witness_v6_minimal.v << 'EOF'
Require Import LMetrics_v6_types.
From Stdlib Require Import Reals Strings.String.

Module witness_v6_minimal.
Definition kappa_eff : R := 3.0.
Definition entropy_eff : R := 0.0.
Definition mass_eff : R := 1.0.
Definition inertial_idx : R := 3.0.
Definition risk_index : R := 3.0.
Definition risk_class := HIGH.
Definition loventre_global_decision := SAFE.
Definition loventre_global_color := GREEN.
Definition loventre_global_score : R := 1.0.
Definition meta_label : string := "meta_v6_seed".
Definition source_file : string := "lmetrics_v6_cli_case_1.json".
End witness_v6_minimal.
EOF

# --- Compila il witness minimale ---
echo "Compilazione witness minimale..."
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_v6_minimal.v || { echo "Errore compiling witness"; exit 3 }

# --- Controlla artefatti .vo generati ---
ls -l Coq_IO/LMetrics_v6/*.vo

