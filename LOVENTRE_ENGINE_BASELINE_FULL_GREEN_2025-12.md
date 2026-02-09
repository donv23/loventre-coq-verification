# LOVENTRE ENGINE – BASELINE FULL GREEN (Dicembre 2025, MacBookAir)

## 0. Contesto

- Mac: **MacBookAir**
- Sistema: **macOS + zsh**
- Python: `/opt/homebrew/bin/python3.13`
- Root motore:
  - `/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed`
- Comando usato:
  - `python3.13 run_loventre_regression_suite.py`

Questa baseline fissa uno stato in cui **tutte le demo Python della regression suite passano** (verde), ad eccezione di due demo volutamente assenti (SKIP).

---

## 1. Stato suite di regressione Python

Output finale rilevante:

- Nessuna demo fallita.
- Demo **SKIP** (file non presenti – comportamento voluto, non errore):
  - `loventre_meta_portfolio_lab.py`
  - `demo_global_entrypoint.py`
- JSON 2-SAT: tutti OK.
- Crosscheck JSON ↔ Coq: nessun mismatch.

### 1.1 Moduli di laboratorio

#### `loventre_global_profile_lab.py`

- Stato: **OK**.
- Funzione: calcolo dei **profili seed (param,factor)** con:
  - `kappa_eff`
  - `entropy_eff`
  - `V0`
  - `p_tunnel(E)`
  - `P_success`
  - `difficulty`
  - `region` (al momento `default_r` per tutta la griglia).
- Parametri di contesto:
  - `E = 0.5`
  - `N_budget = 1000` (tentativi meta per seed).
- La catena interna usa:
  - `build_history_for_seed(...)`
  - `analyze_seed(...)`
  - `analyze_instance(...)` da `loventre_instance_analysis.py`
  - arricchimento con massa e tempo tramite le funzioni di arricchimento del bus.

#### `demo_seed_global_decision.py`

- Stato: **OK**.
- Stampa tabella:

  - colonne: `param`, `factor`, `region`, `P_like`, `NP_like`, `time_regime`, `meta_label`, `risk_class`, `global_decision`, `global_color`, `global_score`.
  - Attualmente:
    - `region = "R00"`
    - `time_regime = time_euclidean`
    - `risk_class = risk_LOW`
    - `meta_label = meta_unknown`
    - blocco globale **non applicato** in questa demo:
      - `global_decision = N/A`
      - `global_color = N/A`
      - `global_score = 0.000`

- Nota di design:
  - La demo seed è pensata come **diagnostica del bus** (senza Policy Bridge).
  - Il blocco globale completo viene esercitato altrove (es. CLI Coq bridge + JSON canonici).

#### `demo_critfam_global_decision.py`

- Stato: **OK**.
- Famiglie critiche testate:

  - `TSP_crit_n`
  - `SAT_crit_n`

- Per entrambe le famiglie, la tabella mostra:

  - `name_or_n`
  - `kappa_eff`
  - `entropy_eff`
  - `V0`
  - `p_tunnel(E)`
  - `P_success`
  - `meta_label`
  - `global_decision` (attualmente `N/A` nella versione di laboratorio)
  - `global_color` (`N/A`)
  - `global_score` (`0.000`)

- I valori di `meta_label` sono coerenti con il disegno:
  - per n piccoli / formule leggere: `P_like_like`
  - regione critica: `NP_like_critico`
  - coda estrema: `NP_like_black_hole`.

#### `demo_mass_global_run.py`

- Stato: **OK** (smoke test).
- Verifica che il wrapper globale sia importabile:

  - Modulo: `loventre_meta_decision_engine`
  - Nome wrapper: `meta_decide_instance_with_mass_global`

- Al momento:
  - La demo **non esegue** realmente il wrapper.
  - Serve come check che l’entrypoint massivo globale esista e sia importabile.
  - In futuro può agganciare:
    - interfacce CLI/Coq,
    - loader JSON/istanze reali,
    - eventuale API esterna.

---

## 2. Stato del Loventre Metrics Bus (Python)

File chiave: `loventre_metrics_bus.py`

### 2.1 API del bus

- Funzioni esposte:

  - `validate_metrics_bus(bus: dict) -> None`
  - `ensure_loventre_keys(bus: dict) -> dict`

- Ruolo:

  - **`validate_metrics_bus`**: controlla che il dizionario `bus` contenga tutte le chiavi canoniche del Loventre Metrics Bus.
    - Se manca una chiave: solleva `KeyError` del tipo
      - `"[LoventreBus] Chiave mancante: <nome_chiave>"`.
  - **`ensure_loventre_keys`**: arricchisce un dizionario parziale con default “Loventre-safe”, poi chiama `validate_metrics_bus`.
    - Garantisce che **tutte** le pipeline a valle vedano sempre un bus completo.

### 2.2 Chiavi canoniche del bus

Il bus finale (dopo `ensure_loventre_keys`) deve sempre avere almeno queste chiavi (nomi **canonici**):

- campi geometrici / entropici:
  - `kappa_eff`
  - `entropy_eff`
  - `V0`
  - `a_min`
  - `p_tunnel`
  - `P_success`
- tempo / massa:
  - `gamma_dilation`
  - `time_regime`
  - `mass_eff`
  - `inertial_idx`
- rischio / profilo:
  - `risk_index`
  - `risk_class`
  - `meta_label`
  - `chi_compactness`
  - `horizon_flag`
- blocco globale (Policy Bridge):
  - `loventre_global_decision`
  - `loventre_global_color`
  - `loventre_global_score`

Questa lista definisce il **Loventre Metrics Bus canonico** per il ponte Python ↔ Coq.

---

## 3. Stato di `loventre_instance_analysis.py`

File chiave per l’analisi di una singola “istanza” (seed, TSP, SAT, …).

### 3.1 API principale

Funzioni visibili (estratto logico):

- `compute_curvature_from_complexity(...)`
- `compute_potential_from_kappa_entropy(...)`
- `estimate_V0_from_U(U_values, quantile: float = 0.9) -> float`
- `estimate_barrier_thickness(U_values, V0: float) -> float`
- `p_tunnel(V0: float, a_min: float, E: float) -> float`
- `expected_attempts(p: float) -> float`
- `analyze_instance(history, instance_name, E: float, w_kappa: float, w_H: float) -> dict`
- `enrich_metrics_with_time_dilation(metrics: dict, E: float, gamma_threshold_hyperbolic: float) -> dict`
- `enrich_metrics_with_mass(metrics: dict) -> dict`
- `suggest_strategy(metrics: dict) -> dict`

### 3.2 Semantica di alto livello

- `analyze_instance(...)`:
  - usa una **history** di punti (seed, TSP, SAT ecc.) per costruire:
    - `kappa_eff`
    - `entropy_eff`
    - `U = α κ + β H`
    - `V0`, `a_min`, `p_tunnel(E)`, `P_success`
  - ritorna un dizionario parziale che viene poi “chiuso” dal bus.
- `enrich_metrics_with_time_dilation(...)`:
  - aggiunge:
    - `gamma_dilation`
    - `time_regime`
  - utilizza il parametro `gamma_threshold_hyperbolic` per decidere transizione verso regime iperbolico.
  - chiama **sempre** `ensure_loventre_keys` prima di restituire il bus.
- `enrich_metrics_with_mass(...)`:
  - specializza:
    - `mass_eff`
    - `inertial_idx`
    - eventuali aggiustamenti su `risk_index` / altri campi coerenti con il modello.
  - anch’essa termina con una chiamata a `ensure_loventre_keys`.

La combinazione di `analyze_instance`, `enrich_metrics_with_time_dilation` e `enrich_metrics_with_mass` produce un **Loventre Metrics Bus completo**, coerente con la lista canonica di chiavi.

---

## 4. Stato del Policy Bridge e decisione globale

File chiave: `loventre_meta_decision_engine.py`

- Wrapper principale (massivo, locale e globale):

  - `loventre_attach_global_decision_to_metrics(metrics: Dict[str, Any], *args, **kwargs) -> Dict[str, Any]`
  - `meta_decide_instance_with_mass(history, E=1.0)`
  - `meta_decide_instance_with_mass_global(history, E=1.0, context=None)`

- Ruolo:

  - leggere il Loventre Metrics Bus,
  - calcolare un **profilo di rischio** interno,
  - applicare il **Policy Bridge** per produrre:
    - `loventre_global_decision`
    - `loventre_global_color`
    - `loventre_global_score`.

### 4.1 Stato nelle demo

- `demo_seed_global_decision.py` e `demo_critfam_global_decision.py`:

  - attualmente mostrano `N/A` per `global_decision/global_color/global_score` nelle tabelle.
  - design attuale:
    - queste demo sono principalmente per **profilare le famiglie** e il bus,
    - la logica di Policy Bridge completa è testata in maniera più mirata (es. CLI Coq bridge, JSON witness).

- `demo_mass_global_run.py`:
  - garantisce che il wrapper globale sia importabile.
  - non esegue ancora una meta-decide completa su istanze reali.

---

## 5. Stato JSON 2-SAT e witness canonici

### 5.1 JSON 2-SAT

- File:
  - `metrics_2SAT_easy_demo.json`
  - `metrics_2SAT_crit_demo.json`
- Stato: **OK_JSON**.
- Semantica:

  - `2SAT_easy`:
    - `meta_label = meta_P_like_like`
    - `risk_class = risk_LOW`
    - `decision = GD_safe`
    - `color = GC_green`
    - `P_success = 1.0`
  - `2SAT_crit`:
    - `meta_label = meta_P_like_accessible`
    - `risk_class = risk_LOW`
    - `decision = GD_borderline`
    - `color = GC_green`
    - `P_success = 1.0`

### 5.2 Witness canonici JSON ↔ Coq

Witness JSON:

- `m_seed11_cli_demo.json`
- `m_TSPcrit28_cli_demo.json`
- `m_SATcrit16_cli_demo.json`
- `m_seed_grid_demo.json`

Crosscheck JSON ↔ Coq (via `Loventre_LMetrics_JSON_Link.v`):

- Tutti gli `lm_id` presenti in Coq hanno un JSON corrispondente e viceversa.
- Convenzione dei file rispettata:
  - `witness_json/<lm_id>.json`
- Nessun mismatch rilevato:
  - struttura ponte **JSON → LMetrics (Coq)** coerente.

---

## 6. Cosa fissa questa baseline

Questa baseline viene usata come **punto di riferimento canonico** per:

1. Stato del codice Python su MacBookAir, Dicembre 2025:
   - suite di regressione **tutta verde** (eccetto demo volutamente assenti).
   - Loventre Metrics Bus **canonico** stabilizzato.
   - arricchimento **massa + tempo** integrato nelle pipeline.
2. Stato del ponte JSON ↔ Coq:
   - 4 witness canonici agganciati (seed11, TSPcrit28, SATcrit16, seed_grid).
3. Stato del Policy Bridge:
   - wrapper globale importabile,
   - decisione globale esercitata principalmente sui witness / JSON dedicati.

Qualsiasi modifica futura al motore Python o al ponte JSON ↔ Coq dovrà essere valutata in rapporto a questa baseline:

- se rompe la suite → regressione non accettabile;
- se la estende → va documentata in un nuovo seed di stato successivo a questo file.

---

