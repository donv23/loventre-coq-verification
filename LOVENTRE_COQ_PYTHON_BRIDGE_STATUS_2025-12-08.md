# LOVENTRE — STATO DEL PONTE COQ ↔ PYTHON (08 dicembre 2025)

Questo file descrive lo stato **operativo** del ponte tra:

- motore Python `LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed`
- progetto Coq `Loventre_Coq_Clean`

La data di riferimento è **08/12/2025** (seed MacBookAir).

---

## 1. Lato Python — Witness JSON e CLI

Root motore:

`/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed`

### 1.1 Witness JSON esportati

Script:

- `loventre_export_witness_json.py`  
- `loventre_witness_json_inspect.py`  
- `loventre_coq_snippet_gen.py`

Directory di output:

- `witness_json/`

Witness JSON principali (allineati a Coq):

- `m_seed11_cli_demo.json`  
- `m_seed_grid_demo.json`  
- `m_TSPcrit28_cli_demo.json`  
- `m_SATcrit16_cli_demo.json`

Per ciascuno, lo script di inspect mostra:

- `role`, `family`, `kind`, `source`
- blocco “Profilo Loventre” con:
  - `meta_label`
  - `risk_class`
  - `horizon_flag`
  - `time_regime`
  - `chi_compactness`
  - `risk_index`
  - `p_tunnel`
- sezione `tags` con `metrics_json_source` e note.

### 1.2 Snippet Coq generati

`loventre_coq_snippet_gen.py` legge i JSON in `witness_json/` e produce snippet Coq del tipo:

```coq
Definition m_seed11_cli_demo : LMetrics := {|
  kappa_eff := _ (* TODO: fill *);
  ...
  p_tunnel := 0.02;
  ...
  risk_index := 2.0;
  risk_class := ...;
  meta_label := ...;
  chi_compactness := 0.2;
  horizon_flag := false;
  ...
|}.

