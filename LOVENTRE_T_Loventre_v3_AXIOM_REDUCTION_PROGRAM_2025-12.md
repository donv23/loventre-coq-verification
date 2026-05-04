# LOVENTRE — PROGRAMMA DI RIDUZIONE ASSIOMI T_Loventre_v3_Prop (Dicembre 2025)

## 0. Scopo

Questo seed descrive un **programma di lavoro** (non una prova)
per analizzare e, se possibile, **ridurre / strutturare meglio** le
ipotesi contenute nella Prop:

- `T_Loventre_v3_Prop`

definita in:

- `03_Main/Loventre_T_Loventre_v3_Prop.v`.

Non modifica alcun file `.v`: è una tab di roadmap concettuale
per futuri interventi in Coq e nella documentazione.

---

## 1. Foto attuale di T_Loventre_v3_Prop

Richiamo della definizione (in Coq):

```coq
Definition T_Loventre_v3_Prop : Prop :=
  (exists m : LMetrics, is_P_like_accessible m) /\
  is_P_like m_seed11_cli_demo /\
  is_P_like m_seed_grid_demo /\
  is_NP_like_black_hole m_TSPcrit28_cli_demo /\
  is_NP_like_black_hole m_SATcrit16_cli_demo.

