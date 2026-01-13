#!/usr/bin/env bash
# audit_v96.sh — V98 Audit canonico
set -e

OUT="03_Main/Docs/Loventre_V96_AUDIT_Report.md"
echo "# Loventre Audit — V96" > "$OUT"
echo "" >> "$OUT"
echo "## Ricerca Axiom" >> "$OUT"
echo '```' >> "$OUT"
grep -R "Axiom" -n . || true >> "$OUT"
echo '```' >> "$OUT"

echo "" >> "$OUT"
echo "## Ricerca Admitted" >> "$OUT"
echo '```' >> "$OUT"
grep -R "Admitted" -n . || true >> "$OUT"
echo '```' >> "$OUT"

echo "" >> "$OUT"
echo "## File senza dipendenze inverse (potenziali candidati refactor)" >> "$OUT"
echo '```' >> "$OUT"
# lista file .v che non vengono importati da altri (solo segnalazione)
for f in $(find . -name "*.v"); do
  hits=$(grep -R "$(basename "$f" .v)" -n . | wc -l)
  if [ "$hits" -le 1 ]; then
    echo "$f"
  fi
done >> "$OUT"
echo '```' >> "$OUT"

echo "" >> "$OUT"
echo "## Conclusione" >> "$OUT"
echo "✔ Audit terminato (Axioms/Admitted e dipendenze analizzate)" >> "$OUT"

echo "" >> "$OUT"
echo "Report scritto in $OUT"

