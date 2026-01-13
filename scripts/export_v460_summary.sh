#!/bin/bash
OUT="03_Main/Docs/Loventre_Main_3SAT_to_BH_v460.md"

(
echo "# Loventre Main — 3SAT → BH Map (V460)"
echo
echo "## Contenuto"
echo "- Definizione mappa map_3SAT_to_BH"
echo "- BH frontier crossing"
echo "- SAFE non preservato"
echo "- Lemma exists_3SAT_to_BH_map"
echo
echo "## File:"
echo "- 02_Advanced/Geometry/Loventre_3SAT_to_BH_Map_v460.v"
echo "- 03_Main/Loventre_Main_3SAT_to_BH_v460.v"
) > "$OUT"

echo "Scritto in $OUT"

