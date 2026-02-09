#!/bin/zsh

# Vai alla root del progetto Loventre Engine
cd ~/Library/"Mobile Documents"/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed || exit 1

# Disabilita errori su glob che non matchano
setopt nullglob

# 1. Pulisci artefatti Coq nella cartella LMetrics_v6
rm -f Coq_IO/LMetrics_v6/*.vos Coq_IO/LMetrics_v6/*.vok Coq_IO/LMetrics_v6/*.glob Coq_IO/LMetrics_v6/*.vio

# 2. Compila LMetrics_v6_types.v
coqc -R Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v || { echo "Errore compiling types"; exit 2 }

# 3. Crea un file witness minimale valido con import Reals corretto
cat > Coq_IO/LMetrics_v6/witness_v6_minimal.v << 'EOF'
Require Import LMetrics_v6_types.
From Coq Require Import Reals.
Open Scope R_scope.

Module witness_v6_minimal.

Definition kappa_eff : R := 3.0.
Definition entropy_eff : R := 0.0.
Definition mass_eff : R := 1.0.
Definition inertial_idx : R := 3.0.
Definition risk_index : R := 3.0.

(* Placeholder numerici per HIGH / SAFE / GREEN *)
Definition risk_class : nat := 1.   (* HIGH *)
Definition loventre_global_decision : nat := 1.  (* SAFE *)
Definition loventre_global_color : nat := 1.     (* GREEN *)

Definition loventre_global_score : R := 1.0.
Definition meta_label := meta_v6_seed.
Definition source_file := "lmetrics_v6_cli_case_1.json".

End.
EOF

# 4. Compila il witness minimale
coqc -R Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_v6_minimal.v || { echo "Errore compiling witness"; exit 3 }

# 5. Controlla i .vo generati
ls -l Coq_IO/LMetrics_v6/*.vo

