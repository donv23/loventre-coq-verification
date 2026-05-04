# LOVENTRE — T_Loventre_v3_Prop (Dicembre 2025)

## 0. Scopo del seed

Questo seed descrive, in linguaggio umano, la Prop:

- `T_Loventre_v3_Prop`

definita in Coq nel file:

- `03_Main/Loventre_T_Loventre_v3_Prop.v`

e il ruolo che gioca rispetto al Teorema principale v3:

- `Loventre_Main_Theorem_v3_Citable_Prop`
- `Loventre_Main_Theorem_v3_from_T_Loventre_v3`.

Non introduce nuove ipotesi: organizza in forma compatta
le assunzioni già descritte nei seed:

- `LOVENTRE_GEOMETRY_AXIOMS_v3_SEED_2025-12.md`
- `LOVENTRE_v3_RIGOROUS_PROGRAM_SEED_2025-12.md`.

---

## 1. Definizione formale di T_Loventre_v3_Prop

Nel file:

- `03_Main/Loventre_T_Loventre_v3_Prop.v`

compare:

```coq
Definition T_Loventre_v3_Prop : Prop :=
  (exists m : LMetrics, is_P_like_accessible m) /\
  is_P_like m_seed11_cli_demo /\
  is_P_like m_seed_grid_demo /\
  is_NP_like_black_hole m_TSPcrit28_cli_demo /\
  is_NP_like_black_hole m_SATcrit16_cli_demo.

