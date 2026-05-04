# LAB-12.4 — Global Rigidity via Reachability (v0)

**Stato:** LAB IMPOSSIBILE (tautologia per vacuità)
**Data:** Gennaio 2026

## Diagnosi

La definizione:

GlobalRigid_reach := ~ Reach_Decomposable

collassa perché:

- Reach_Decomposable richiede l'esistenza di una partizione non banale
- Il Core non garantisce che Config abbia cardinalità ≥ 2
- Quindi Reach_Decomposable è falso in generale
- GlobalRigid_reach risulta vera per vacuità

## Conclusione

Questa versione di rigidità globale:
- non è pairwise
- ma è comunque tautologica
- fallisce per debolezza del dominio

Il LAB è archiviato come risultato negativo strutturale.

