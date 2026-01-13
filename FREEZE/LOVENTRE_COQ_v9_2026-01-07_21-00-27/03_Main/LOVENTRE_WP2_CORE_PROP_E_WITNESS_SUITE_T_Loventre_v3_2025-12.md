# LOVENTRE — WP2: Core Prop & Witness Suite per v3/v3+ (Dicembre 2025)
Versione: v1.0 — Data: 2025-12

## 0. Scopo (WP2)
Fissare una struttura concettuale a livelli (senza modificare `.v`) per sostituire l’uso monolitico di
`T_Loventre_v3_Prop` con:

- una **Core Prop** minima per il teorema principale;
- una **Core Prop** minima per la separazione di classi;
- una **WitnessSuite Prop** ricca (regressione + robustezza);
- un mapping esplicito: `WitnessSuite -> CoreMain` e `WitnessSuite -> CoreClassSep`.

Vincoli:
- Nessuna modifica ai `.v` in questo WP2.
- Nessun ponte implicito tra `is_P_like_accessible` e `is_P_like` (per ora NON esiste).

---

## 1. Dati di fatto emersi da WP0/WP1 (riassunto)

1) `Loventre_Main_Theorem_v3.v` usa davvero solo:
- `is_P_like m_seed11_cli_demo`
- `is_NP_like_black_hole m_TSPcrit28_cli_demo`

2) `Loventre_Class_Separation_v3.v` usa davvero:
- `is_NP_like_black_hole m_TSPcrit28_cli_demo`
- `~ is_P_like_accessible m_TSPcrit28_cli_demo`

3) `is_P_like_accessible` è predicato astratto e indipendente da `is_P_like`.
Quindi:
- non è lecito “derivare P_like” da “P_accessible” senza introdurre un ponte.

4) Esiste già un’ancora canonica v3+:
- `is_P_like_accessible m_seed_grid_demo`
(importata dal layer `Loventre_Test_Pacc_2SAT_Profile_v3` e riassunta in `Loventre_Axioms_v3_Summary`).

---

## 2. Definizioni target (solo concettuali)

### 2.1 CoreMain (minimo reale usato dal teorema principale v3)
Obiettivo: pacchetto minimale che basta per `Loventre_Main_Theorem_v3_Prop`.

```coq
Definition T_Loventre_v3_CoreMain_Prop : Prop :=
  is_P_like m_seed11_cli_demo /\
  is_NP_like_black_hole m_TSPcrit28_cli_demo.

