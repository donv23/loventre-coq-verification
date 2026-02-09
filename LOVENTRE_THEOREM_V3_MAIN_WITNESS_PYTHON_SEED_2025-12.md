# LOVENTRE_THEOREM_V3_MAIN_WITNESS_PYTHON_SEED – dicembre 2025

_Seed Python per i witness principali del Main Theorem v3_

Root motore Python:
`/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed`

Questo file fissa, lato Python, **quali JSON** e **quali script**
realizzano concretamente la tripla astratta:

- `m_P`    : fase P_like,
- `m_Pacc` : fase P_like_accessible,
- `m_NP`   : fase NP_like_critica **NON SAFE**,

che compare in Coq nella proposizione:

```coq
Loventre_Main_Prop : Prop :=
  exists (m_P m_Pacc m_NP : LMetrics),
    P_like_complexity_profile m_P /\
    P_like_accessible_profile m_Pacc /\
    NP_like_crit_profile m_NP /\
    loventre_global_decision m_NP <> GD_safe.

