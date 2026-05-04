# LOVENTRE MAIN THEOREM v3 — NOTA CITABILE (Dicembre 2025)

## 0. Contesto

Questa nota accompagna i file Coq:

- `03_Main/Loventre_Main_Theorem_v3_Citable.v`
- `03_Main/Loventre_T_Loventre_v3_Prop.v`

e i seed:

- `LOVENTRE_T_Loventre_v3_Prop_SEED_2025-12.md`
- `LOVENTRE_v3_RIGOROUS_PROGRAM_SEED_2025-12.md`

Scopo: rendere leggibile come **enunciato matematico classico**  
il risultato formalizzato e dimostrato in Coq.

---

## 1. Ipotesi del modello (T_Loventre_v3_Prop)

Si assumono le ipotesi T_Loventre_v3_Prop, cioè:

1. Esiste almeno un profilo P_like_accessible nel tipo LMetrics.  
2. I witness `m_seed11_cli_demo` e `m_seed_grid_demo` sono P_like.  
3. I witness `m_TSPcrit28_cli_demo` e `m_SATcrit16_cli_demo`
   sono NP_like_black_hole.

Formalmente (in Coq):

```coq
Definition T_Loventre_v3_Prop : Prop :=
  (exists m : LMetrics, is_P_like_accessible m) /\
  is_P_like m_seed11_cli_demo /\
  is_P_like m_seed_grid_demo /\
  is_NP_like_black_hole m_TSPcrit28_cli_demo /\
  is_NP_like_black_hole m_SATcrit16_cli_demo.

