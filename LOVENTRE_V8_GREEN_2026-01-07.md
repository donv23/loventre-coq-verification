# LOVENTRE — V8 GREEN FREEZE (07 Gennaio 2026)

## Stato
Congelamento versione V8 del modello Loventre in Coq.

### Componenti resi verdi e stabili
- Bus V7 → record `LMetrics`
- Traduttori JSON → Bus
- Bridge `v7_Witness_From_Bus → v8`
- SAFE layer (`Loventre_LMetrics_v8_SAFE.v`)
- POLICY layer (`Loventre_LMetrics_v8_Policy.v`)
- RISK layer (`Loventre_LMetrics_v8_Risk.v`)
- MetaDecision (`Loventre_LMetrics_v8_MetaDecision.v`)
- Composizione logica:
  - `All_In_One`
  - `Citable`
  - `Suite` con i 4 witness bus seed

### Witness validati in configurazione V8
- seed11
- TSPcrit28
- 2SAT_easy
- 2SAT_crit

Tutti i witness compilano correttamente nel modello V8.

### Proprietà ottenute
- Disponibilità di `loventre_global_decision_v8`
- SAFE/Policy/Risk integrati
- Pipeline chiusa su 4 casi reali

## Regole
Questo snapshot deve restare invariato.
Ogni modifica a V8 richiede clonazione in 99_LEGACY/V8_*
Il lavoro nuovo va proposto come V9+.

## Prossimo Canvas
Canvas 11 — Horizon & Black-Hole
- estendere la classificazione
- introdurre lemma `bh_like?`
- nessuna modifica distruttiva sui file V8

## Nota Storica
V8 rappresenta la prima versione completa e stabile del motore Coq
che collega seeds reali (JSON) → Bus → SAFE/RISK → MetaDecision
con output verificabile e testato.

