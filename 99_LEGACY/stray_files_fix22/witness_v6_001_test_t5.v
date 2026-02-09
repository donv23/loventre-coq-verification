#!/bin/zsh

# ============================
# Script patch + compilazione
# ============================

# Vai alla root del progetto
cd ~/Library/"Mobile Documents"/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed

# Evita errori se non ci sono file
setopt nullglob

# Pulizia artefatti Coq vecchi
rm -f Coq_IO/LMetrics_v6/*.vos Coq_IO/LMetrics_v6/*.vok Coq_IO/LMetrics_v6/*.glob Coq_IO/LMetrics_v6/*.vio

# Definisci i file witness da correggere
WITNESSES=(Coq_IO/LMetrics_v6/witness_v6_*.v)

# Loop su tutti i witness
for f in "${WITNESSES[@]}"; do
    echo "Patching $f ..."

    # Sostituisci numeri decimali nei campi nat
    sed -i '' -E 's/([[:space:]]+: nat := )([0-9]+)\.0;/\1\2;/g' "$f"

    # Sostituisci costanti mancanti con quelle definite in LMetrics_v6_types
    sed -i '' -E 's/\bGREEN\b/GREEN/g' "$f"
    sed -i '' -E 's/\bHIGH\b/HIGH/g' "$f"
    sed -i '' -E 's/\bSAFE\b/SAFE/g' "$f"

    # Se ci sono campi mass_eff, entropy_eff ecc. di tipo R usa numeri con punto
    sed -i '' -E 's/([[:space:]]+: R := )([0-9]+);/\1\2.0;/g' "$f"
done

echo "Correzione completata. Compilazione dei file..."

# Compila types prima di tutto
coqc -Q Coq_IO/LMetrics_v6 LMetrics_v6 Coq_IO/LMetrics_v6/LMetrics_v6_types.v

# Compila tutti i witness
for f in "${WITNESSES[@]}"; do
    coqc -R Coq_IO/LMetrics_v6 LMetrics_v6 "$f"
done

echo "Compilazione completata. Controllo dei .vo generati:"
ls -l Coq_IO/LMetrics_v6/*.vo

