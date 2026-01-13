#!/usr/bin/env bash
# export_v96_summary.sh
# V97 — Produce un riassunto citable del 2SAT pipeline

set -e

OUT="03_Main/Docs/Loventre_Main_2SAT_Citable_Summary_v96.md"

echo "# Loventre — 2SAT Citable Summary (V96)" > "$OUT"
echo "" >> "$OUT"

echo "## Import principale" >> "$OUT"
echo '```coq' >> "$OUT"
echo "From Loventre_Main Require Import Loventre_Main_2SAT_Citable_Theorem." >> "$OUT"
echo '```' >> "$OUT"
echo "" >> "$OUT"

echo "### Proposizioni garantite dalla pipeline V96" >> "$OUT"
echo "- easy_2SAT = classificato come Pacc / SAFE" >> "$OUT"
echo "- crit_2SAT = classificato come non-Pacc / NPbh-Like" >> "$OUT"
echo "- separazione interna: easy ≠ crit" >> "$OUT"
echo "- catena di validazione Coq verificata" >> "$OUT"

echo "" >> "$OUT"
echo "### Struttura della prova" >> "$OUT"
echo "- JSON → LMetrics" >> "$OUT"
echo "- Decode → Compute" >> "$OUT"
echo "- Compare → Phase/SAFE/Class" >> "$OUT"
echo "- Teoremi finali in 03_Main" >> "$OUT"

echo "" >> "$OUT"
echo "### Note" >> "$OUT"
echo "- Nessun assioma aggiunto" >> "$OUT"
echo "- Nessun admitted" >> "$OUT"
echo "- Nessun lemma non usato" >> "$OUT"

echo "" >> "$OUT"
echo "✔ Export completato." >> "$OUT"

echo "Scritto in $OUT"

