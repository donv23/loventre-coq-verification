#!/bin/zsh

# --- Root del progetto Loventre Engine ---
cd ~/Library/"Mobile Documents"/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed || exit 1

# --- Pulisci artefatti Coq ---
rm -f Coq_IO/LMetrics_v6/*.vos Coq_IO/LMetrics_v6/*.vok Coq_IO/LMetrics_v6/*.glob Coq_IO/LMetrics_v6/*.vio

# --- Compila types file ---
echo "Compilazione LMetrics_v6_types.v..."
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v || { echo "Errore compiling types"; exit 2 }

# --- Crea il witness minimale ---
cat > Coq_IO/LMetrics_v6/witness_v6_minimal.v << 'EOF'
Require Import LMetrics_v6_types.
From Stdlib Require Import Reals.
From Stdlib Require Import Strings.String.

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
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_v6_minimal.v || { echo "Errore compiling witness minimale"; exit 3 }

# --- Crea automaticamente witness derivati (esempio parametrici) ---
for i in {1..10}; do
  cat > Coq_IO/LMetrics_v6/witness_v6_derived_$i.v << EOF
Require Import LMetrics_v6_types.
Require Import witness_v6_minimal.

Module witness_v6_derived_$i.
Definition kappa_eff := witness_v6_minimal.kappa_eff + $i.
Definition entropy_eff := witness_v6_minimal.entropy_eff.
Definition mass_eff := witness_v6_minimal.mass_eff.
Definition inertial_idx := witness_v6_minimal.inertial_idx.
Definition risk_index := witness_v6_minimal.risk_index.
Definition risk_class := witness_v6_minimal.risk_class.
Definition loventre_global_decision := witness_v6_minimal.loventre_global_decision.
Definition loventre_global_color := witness_v6_minimal.loventre_global_color.
Definition loventre_global_score := witness_v6_minimal.loventre_global_score.
Definition meta_label := witness_v6_minimal.meta_label.
Definition source_file := witness_v6_minimal.source_file.
End witness_v6_derived_$i.
EOF
  coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_v6_derived_$i.v || { echo "Errore compiling witness_v6_derived_$i"; exit 4 }
done

# --- Controlla tutti i .vo generati ---
echo "Controllo artefatti .vo:"
ls -l Coq_IO/LMetrics_v6/*.vo

