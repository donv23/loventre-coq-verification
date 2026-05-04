# LOVENTRE — Programma di Riduzione Assiomi per T_Loventre_v3_Prop (Dicembre 2025)
Versione: v1.0 — Data: 2025-12

## 0. Scopo e vincoli

**Scopo**
- Definire un programma di lavoro (roadmap concettuale) per analizzare e, se possibile,
  **ridurre / strutturare meglio** le ipotesi contenute in:
  - `T_Loventre_v3_Prop` (file: `03_Main/Loventre_T_Loventre_v3_Prop.v`)

**Vincoli**
- Questo documento **non modifica alcun file `.v`**.
- Nessuna rivendicazione su P≠NP classico: qui si parla solo di separazioni **nel modello Loventre** (P-like / P-like-accessible / NP-like-black-hole).
- I witness citati qui sono **canonici** (CLI demo + bridge JSON/LMetrics già stabilizzato).

---

## 1. Foto attuale della Prop (per riferimento)

Definizione attuale (riportata come foto):

```coq
Definition T_Loventre_v3_Prop : Prop :=
  (exists m : LMetrics, is_P_like_accessible m) /\
  is_P_like m_seed11_cli_demo /\
  is_P_like m_seed_grid_demo /\
  is_NP_like_black_hole m_TSPcrit28_cli_demo /\
  is_NP_like_black_hole m_SATcrit16_cli_demo.

