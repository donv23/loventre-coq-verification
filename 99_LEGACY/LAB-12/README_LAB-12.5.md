# LAB-12.5 — Conditional Global Rigidity (v1)

**Stato:** LAB IMPOSSIBILE (vacuità dell’ipotesi)
**Data:** Gennaio 2026

## Diagnosi

La definizione:

GlobalRigid_reach_cond :=
  Two_Disjoint_Basins -> ~ Reach_Decomposable_cond

collassa perché:

- Two_Disjoint_Basins è una proposizione non garantita dal Core
- Un'implicazione con antecedente non dimostrabile
  è vera per vacuità
- GlobalRigid_reach_cond risulta dimostrabile senza ipotesi

## Conclusione strutturale

Condizionare una rigidità globale tramite una proposizione astratta
NON è sufficiente.

La condizione deve essere:
- strutturale
- incarnata in un modello
- non eliminabile logicamente

Questo LAB fornisce un nuovo failure mode:
"Vacuità dell’ipotesi condizionale".

LAB archiviato come risultato negativo CANONICO.

