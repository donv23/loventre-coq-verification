#!/bin/zsh

# Vai alla root del progetto Loventre Engine
cd ~/Library/"Mobile Documents"/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed || exit 1

# Disabilita errori se non ci sono file corrispondenti
setopt nullglob

# Pulisci artefatti Coq nella cartella LMetrics_v6
rm -f Coq_IO/LMetrics_v6/*.vos Coq_IO/LMetrics_v6/*.vok Coq_IO/LMetrics_v6/*.glob Coq_IO/LMetrics_v6/*.vio

# --- FIX 150.11 ---
# 1. Riscriviamo LMetrics_v6_types.v con tutte le costanti necessarie
cat > Coq_IO/LMetrics_v6/LMetrics_v6_types.v << 'EOF'
From Stdlib Require Import Reals.

(* Tipi principali *)
Inductive RiskClass := LOW | MEDIUM | HIGH.
Inductive LoventreDecision := SAFE | UNSAFE.
Inductive Color := RED | YELLOW | GREEN.

(* Meta label placeholder *)
Definition meta_v6_seed := 1.

(* Tipi base per il witness *)
Record LMetrics := mkLMetrics {
  kappa_eff : R;
  entropy_eff : R;
  mass_eff : R;
  inertial_idx : R;
  risk_index : R;
  risk_class : RiskClass;
  loventre_global_decision : LoventreDecision;
  loventre_global_color : Color;
  loventre_global_score : R;
  meta_label : nat;
  source_file : string
}.
EOF

# 2. Compila il types file
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v || { echo "Errore compiling types"; exit 2 }

# 3. Crea un witness minimale coerente
cat > Coq_IO/LMetrics_v6/witness_v6_minimal.v << 'EOF'
Require Import LMetrics_v6_types.
From Stdlib Require Import Reals.

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
Definition meta_label := meta_v6_seed.
Definition source_file := "lmetrics_v6_cli_case_1.json".
End.
EOF

# 4. Compila il witness minimale
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_v6_minimal.v || { echo "Errore compiling witness"; exit 3 }

# 5. Controlla i .vo generati
ls -l Coq_IO/LMetrics_v6/*.vo

