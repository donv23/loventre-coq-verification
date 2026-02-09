#!/bin/zsh
# ------------------------------------------------------------
# Script fix150.14 — Loventre Engine LMetrics_v6
# Obiettivo: creare witness minimale funzionante e .vo compilati
# Versione canvas: v1150.150.14
# ------------------------------------------------------------

# 1. Vai alla root del progetto Loventre Engine
cd ~/Library/"Mobile Documents"/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed || exit 1

# 2. Disabilita errori su glob vuoti
setopt nullglob

# 3. Pulisci tutti gli artefatti Coq nella cartella LMetrics_v6
rm -f Coq_IO/LMetrics_v6/*.vos Coq_IO/LMetrics_v6/*.vok Coq_IO/LMetrics_v6/*.glob Coq_IO/LMetrics_v6/*.vio

# 4. Compila LMetrics_v6_types.v
echo "Compilazione LMetrics_v6_types.v..."
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v || { echo "Errore compilazione types"; exit 2 }

# 5. Crea il witness minimale funzionante
echo "Creazione witness minimale..."
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
(* meta_label := meta_v6_seed → da aggiungere nel types file futuro *)
Definition source_file := "lmetrics_v6_cli_case_1.json".
End.
EOF

# 6. Compila il witness minimale
echo "Compilazione witness minimale..."
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/witness_v6_minimal.v || { echo "Errore compilazione witness"; exit 3 }

# 7. Controlla i .vo generati
echo "Verifica .vo generati..."
ls -l Coq_IO/LMetrics_v6/*.vo

echo "Fix150.14 completato: witness minimale compilato correttamente."

