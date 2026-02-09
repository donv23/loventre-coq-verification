#!/bin/zsh
# ------------------------------------------------------------
# Fix150.16 — Compilazione LMetrics_v6 + witness minimale string-safe
# Canvas v1150.150.16
# ------------------------------------------------------------

cd ~/Library/"Mobile Documents"/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed || exit 1

# Disabilita errori su glob vuoti
setopt nullglob

# Pulisci artefatti precedenti
rm -f Coq_IO/LMetrics_v6/*.vos Coq_IO/LMetrics_v6/*.vok Coq_IO/LMetrics_v6/*.glob Coq_IO/LMetrics_v6/*.vio

# Compila il types file
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v || { echo "Errore compilazione types"; exit 2 }

# Crea witness minimale con string-safe
cat > Coq_IO/LMetrics_v6/witness_v6_minimal.v << 'EOF'
Require Import LMetrics_v6.LMetrics_v6_types.
From Stdlib Require Import Reals.
From Coq Require Import Strings.String.

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
Definition source_file : string := "lmetrics_v6_cli_case_1.json".
End.
EOF

# Compila il witness
coqc -R Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_v6_minimal.v || { echo "Errore compilazione witness"; exit 3 }

# Controlla i .vo generati
ls -l Coq_IO/LMetrics_v6/*.vo

