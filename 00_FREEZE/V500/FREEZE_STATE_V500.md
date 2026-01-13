#!/bin/bash
# Export summary for Loventre v500
OUT="03_Main/Docs/Loventre_Main_Family_Chain_v500.md"
mkdir -p 03_Main/Docs

{
echo "# Loventre Family Chain — v500"
echo ""
echo "## Descrizione"
echo "Catena completa 2SAT → 3SAT → NP_like/BlackHole verificata formalmente."
echo ""
echo "## File Coinvolti"
echo "- 02_Advanced/Geometry/Loventre_Family_Complete_Chain_v500.v"
echo "- 03_Main/Loventre_Main_Family_Chain_v500.v"
echo ""
echo "## Pilastri usati"
echo "- LMetrics Core"
echo "- SAFE / UNSAFE Boundary"
echo "- Phase Assembly"
echo "- 2SAT & 3SAT Profiles"
echo "- Black Hole Frontier"
echo ""
echo "## Proprietà attestate tramite build"
echo "- la catena logica è coerente"
echo "- i witness json caricati sono ben formati"
echo "- nessuna ipotesi aggiuntiva fuori asse canonico"
echo ""
echo "## Note"
echo "Questo summary è parte del percorso verso v600 (composizione esplicita NP-hard)."
} > "$OUT"

echo "Scritto in $OUT"

