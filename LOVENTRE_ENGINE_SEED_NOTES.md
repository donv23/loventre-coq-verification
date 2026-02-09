### Stato regressione – MacBookAir (dicembre 2025)

- Nessuna demo fallita.
- Nessuna demo saltata.
- Tutti i JSON 2-SAT (`metrics_2SAT_easy_demo.json`, `metrics_2SAT_crit_demo.json`) validati.
- Crosscheck JSON ↔ Coq (witness canonici) muto e coerente:
  - `m_seed11_cli_demo`
  - `m_seed_grid_demo`
  - `m_TSPcrit28_cli_demo`
  - `m_SATcrit16_cli_demo`

Demo attive:

- `loventre_meta_portfolio_lab.py`  
  Riepilogo “meta-portfolio” di:
  - 9 seed `seed_{param}_{factor}`
  - famiglie critiche `SAT_crit16`, `TSP_crit28`  
  con `risk_class`, `meta_label`, `Strategy` via `suggest_strategy`.

- `loventre_global_profile_lab.py`  
  Profili completi per i 9 seed (param,factor) con:
  - `kappa_eff`, `entropy_eff`, `V0`, `p_tunnel(E)`, `P_success`, `difficulty`.

- `demo_seed_global_decision.py`  
  Griglia seed_grid con:
  - `time_regime`, `meta_label`, `risk_class`, campi global decision/color/score presenti ma non ancora attivati (N/A / 0.0 per scelta).

- `demo_critfam_global_decision.py`  
  Profili TSP_crit_n e SAT_crit_n con:
  - `kappa_eff`, `entropy_eff`, `V0`, `p_tunnel(E)`, `P_success`, `meta_label`, campi global decision/color/score placeholder (N/A / 0.0).

- `demo_mass_global_run.py`  
  Smoke test del wrapper globale:
  - `meta_decide_instance_with_mass_global` importabile da `loventre_meta_decision_engine`.

- `demo_cli_coq_bridge.py`  
  Ponte CLI `metrics JSON → Policy Bridge → LMetrics → snippet Coq` funzionante per tutti e 4 i witness canonici.

- `demo_global_entrypoint.py`  
  Bootstrap test:
  - import di `loventre_instance_analysis`, `loventre_metrics_bus`, `loventre_meta_decision_engine` OK.
  - conferma che il motore è avviabile come sistema.

Conclusione:  
**Baseline Loventre Engine (MacBookAir) = FULL GREEN** su:
- motore Python (seed_grid, famiglie critiche, wrapper globale),
- JSON 2-SAT,
- ponte JSON ↔ LMetrics Coq.

