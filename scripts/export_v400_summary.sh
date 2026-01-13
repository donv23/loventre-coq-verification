#!/bin/bash
set -e

OUTDIR="03_Main/Docs"
OUTFILE="$OUTDIR/Loventre_Main_Family_Theorem_v400.md"

mkdir -p "$OUTDIR"

cat > "$OUTFILE" << 'EOF'
# Loventre Main Family Theorem — V400 (Gennaio 2026)

## Stato del modello
Versione interna: **V400**
Famiglia coperta:
- 2SAT easy
- 2SAT critical
- 3SAT easy
- 3SAT critical

Bridge fondamentali usati:
- LMetrics Core + Structure
- SAFE Model
- Class Model
- Phase Assembly
- Family Aggregators
- 2SAT/3SAT Bridges
- SAFE / UNSAFE Bridges

## Statement del Teorema V400 (modello Loventre)

Nel modello Loventre v400, verificato nella compilazione Coq:

1. **Ogni istanza SAFE appartiene a `Loventre_Pacc_class`**
   - Formale:  
     ∀ m, SAFE(m) → Pacc(m)

2. **Esiste almeno un’istanza NON-SAFE**
   - Formale:  
     ∃ m₀, ¬ SAFE(m₀)

3. **L’istanza NON-SAFE appartiene a `Loventre_NP_blackhole_class`**
   - Formale:  
     ∃ m₀, NP_bh(m₀)

4. **La classe Pacc NON contiene tutta la famiglia**
   - Formale:  
     Pacc ⊂ Family

5. **Esiste una separazione strutturale interna, senza assiomi extra**
   - Pacc ≠ Family
   - Family ∩ NP_bh ≠ ∅

## Interpretazione naturale

La famiglia dei problemi osservata nel dominio Loventre:
- Include sottocasi **risolvibili in modo sicuro (SAFE)**  
  classificati come **Pacc**
- Include sottocasi con comportamento **non controllabile (UNSAFE)**  
  classificati come **NP_black_hole**

→ La frontiera logica separa due mondi:
- **Soluzioni stabili/controllate**
- **Soluzioni che collassano sotto rischio/entropia/tunneling**

## Relazione con il programma del Teorema

Questa è la prima versione che dimostra formalmente:
- SAFE ↔ Pacc (traccia positiva)
- Esistenza di un OUTLIER non SAFE
- Inclusione del OUTLIER nel mondo NP_black_hole

È dunque:
- un **proto-teorema di separazione interno**,
- un **punto fermo della teoria Loventre**.

## Prossima Roadmap

- V430: Frontiera Pacc/NPbh
- V460: SAFE → BH transition formalizzata
- V500: Classificazione a +4 classi operative
  (easy Pacc, crit Pacc, soft NPbh, deep NPbh)

---
(Documento generato automaticamente)
EOF

echo "Scritto in $OUTFILE"

