# LOVENTRE_NP_CRITICAL_GUARD_SEED – dicembre 2025

_Asse: NP_like-black-hole ≠ SAFE / ≠ GREEN (vista Python)_

Root Python:
`/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed`

Script chiave:

- `loventre_complexity_profile_view.py`  
  → classifica i `metrics_*.json` nei profili:
  - `P_like_complexity_profile`  (LOW + non black-hole),
  - `NP_like_crit_complexity_profile` (NP_like_black_hole + black-hole),
  allineati a `Loventre_LMetrics_Complexity_Profiles.v`.

- `loventre_np_critical_guard.py`  
  → guardiano operativo per le istanze NP_like_crit_complexity.

---

## 1. Definizione operativa dei profili NP_critici

Profili usati in entrambi gli script:

- `P_like_complexity_profile` (lato JSON):

  ```text
  risk_class ∈ {LOW, risk_LOW}
  e horizon_flag = false

