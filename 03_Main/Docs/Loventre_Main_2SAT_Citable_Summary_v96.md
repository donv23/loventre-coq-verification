# Loventre — 2SAT Citable Summary (V96)

## Import principale
```coq
From Loventre_Main Require Import Loventre_Main_2SAT_Citable_Theorem.
```

### Proposizioni garantite dalla pipeline V96
- easy_2SAT = classificato come Pacc / SAFE
- crit_2SAT = classificato come non-Pacc / NPbh-Like
- separazione interna: easy ≠ crit
- catena di validazione Coq verificata

### Struttura della prova
- JSON → LMetrics
- Decode → Compute
- Compare → Phase/SAFE/Class
- Teoremi finali in 03_Main

### Note
- Nessun assioma aggiunto
- Nessun admitted
- Nessun lemma non usato

✔ Export completato.
