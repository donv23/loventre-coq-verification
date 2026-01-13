#!/bin/bash
OUT="03_Main/Docs/Loventre_Main_Family_SAFE_BH_Frontier_v430.md"
mkdir -p 03_Main/Docs
echo "# Loventre SAFE ↔ BlackHole Frontier — V430" > $OUT
echo "" >> $OUT
echo "## Risultato" >> $OUT
echo "- SAFE implica NON BlackHole" >> $OUT
echo "- BlackHole implica NON SAFE" >> $OUT
echo "- Insime disgiunti" >> $OUT
echo "" >> $OUT
echo "## File Coq" >> $OUT
echo "- 02_Advanced/Geometry/Loventre_Family_SAFE_BH_Frontier_v430.v" >> $OUT
echo "- 03_Main/Loventre_Main_Family_SAFE_BH_Frontier_v430.v" >> $OUT
echo "" >> $OUT
echo "OK" >> $OUT
echo "Scritto in $OUT"

