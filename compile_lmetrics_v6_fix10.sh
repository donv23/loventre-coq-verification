#!/bin/zsh

# === Fix 10: compile LMetrics v6 minimale senza errori ===

# 1. Vai alla root del progetto Loventre Engine
cd ~/Library/"Mobile Documents"/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed || { echo "Cannot cd to root"; exit 1 }

# 2. Disabilita errori su glob che non matchano
setopt nullglob

# 3. Pulisci tutti gli artefatti Coq nella cartella LMetrics_v6
rm -f Coq_IO/LMetrics_v6/*.vos Coq_IO/LMetrics_v6/*.vok Coq_IO/LMetrics_v6/*.glob Coq_IO/LMetrics_v6/*.vio

# 4. Compila il file types
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v || { echo "Errore compiling types"; exit 2 }

# 5. Crea un witness minimale con placeholder validi
cat > Coq_IO/LMetrics_v6/witness_v6_minimal.v << 'EOF'
Require Import LMetrics_v6_types.
From Stdlib Require Import Reals.

Module witness_v6_minimal.

(* Placeholder numerici *)
Definition kappa_eff : R := 3.0.
Definition entropy_eff : R := 0.0.
Definition mass_eff : R := 1.0.
Definition inertial_idx : R := 3.0.
Definition risk_index : R := 3.0.

(* Placeholder per tipi enumerati *)
Definition risk_class := HIGH.
Definition loventre_global_decision := SAFE.
Definition loventre_global_color := GREEN.

(* Placeholder meta_label *)
Definition meta_label : R := 0.0.

(* File di origine *)
Definition source_file := "lmetrics_v6_cli_case_1.json".

End.
EOF

# 6. Compila il witness minimale
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_v6_minimal.v || { echo "Errore compiling witness"; exit 3 }

# 7. Controlla i .vo generati
ls -l Coq_IO/LMetrics_v6/*.vo

