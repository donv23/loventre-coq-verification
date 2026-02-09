**MINI-SEED SYNC — PROGETTO LOVENTRE ENGINE (tab parallela, dicembre 2025)**

---

### 1. Contesto e path

* Root Python attuale (Loventre Engine):
  `.../ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed`

* Questo mini-seed è il “gemello” Python del seed Coq:
  `MINI-SEED SYNC — PROGETTO LOVENTRE COQ (tab parallela, dicembre 2025)`
  → le due tab devono essere sempre tenute allineate.

---

### 2. Stato tecnico attuale (riassunto Engine)

**Script principale di regressione**

* `run_loventre_regression_suite.py`

  * Attualmente termina con:

    * ✅ nessuna demo fallita
    * ✅ nessun JSON 2-SAT fallito
    * ✅ crosscheck JSON ↔ Coq **OK** (nessun mismatch)

**Demo chiave / moduli testati nella suite**

* `loventre_meta_portfolio_lab.py`

  * Stampa tabella degli 11 seed (griglia 3×3 + SAT_crit16 + TSP_crit28) con:

    * `risk_class` ∈ {`risk_LOW`, `risk_MID`, `risk_NP_like_black_hole`}
    * `meta_label` ∈ {`meta_P_like_like`, `meta_P_like_accessible`, `meta_NP_like_black_hole`}
    * action string “SAFE / ACCESSIBLE / CRITICAL”.

* `loventre_global_profile_lab.py`

  * Profilo della griglia `(param, factor) ∈ {1,2,3}²`:

    * `kappa_eff`, `entropy_eff`, `V0`, `p_tunnel(E)`, `P_success`, `difficulty`.

* `demo_seed_global_decision.py`

  * Usa `metrics_seed11_cli_demo.json`
  * Mostra il blocco `global_decision_label`, `global_decision_score`, `meta_explanation` + meta-info `meta_label`, `risk_class`, `horizon_flag`.

* `demo_critfam_global_decision.py`

  * Usa `metrics_SAT_crit16_demo.json` e `metrics_TSP_crit28_demo.json`
  * Entrambi NP-like black hole a livello di `risk_class`/`meta_label` con `horizon_flag = True`.

* `demo_mass_global_run.py`

  * Verifica che il wrapper globale:

    * modulo: `loventre_meta_decision_engine`
    * nome: `meta_decide_instance_with_mass_global`
      sia importabile (smoke test).

* `demo_global_entrypoint.py`

  * Verifica import di:

    * `loventre_instance_analysis`
    * `loventre_metrics_bus`
    * `loventre_meta_decision_engine`.

* `demo_cli_coq_bridge.py`

  * Chiama `loventre_metrics_cli_coq_bridge.py` su:

    * `metrics_seed11_cli_demo.json  → m_seed11_cli_demo`
    * `metrics_TSPcrit28_demo.json  → m_TSPcrit28_cli_demo`
    * `metrics_SATcrit16_demo.json  → m_SATcrit16_cli_demo`
    * `metrics_seed_grid_demo_global.json → m_seed_grid_demo`
  * Stampa snippet Coq `Definition m_... : LMetrics := {| ... |}.`

* `loventre_json_crosscheck_coq.py`

  * Controlla l’allineamento tra:

    * JSON in `witness_json/`
    * file Coq link `Loventre_LMetrics_JSON_Link.v`
  * Stato attuale: **OK** su tutti i 6 `lm_id`:

    * `m_2SAT_crit_demo`, `m_2SAT_easy_demo`
    * `m_SATcrit16_cli_demo`, `m_TSPcrit28_cli_demo`
    * `m_seed11_cli_demo`, `m_seed_grid_demo`.

---

### 3. Witness canonici (Python ↔ Coq)

**Witness 4 principali (già agganciati a Coq v3)**

* `witness_json/m_seed11_cli_demo.json`
  ↔ `m_seed11_cli_demo : LMetrics`

  * Interpretabile come seed P-like / SAFE.

* `witness_json/m_seed_grid_demo.json`
  ↔ `m_seed_grid_demo : LMetrics`

  * Regime di calibrazione / profilo di griglia.

* `witness_json/m_TSPcrit28_cli_demo.json`
  ↔ `m_TSPcrit28_cli_demo : LMetrics`

  * Witness NP-like black hole (TSP critico).

* `witness_json/m_SATcrit16_cli_demo.json`
  ↔ `m_SATcrit16_cli_demo : LMetrics`

  * Witness critico SAT.

**Witness 2-SAT (famiglia introdotta di recente)**

* `witness_json/m_2SAT_easy_demo.json`
  ↔ `m_2SAT_easy_demo : LMetrics` (Coq)

  * 2-SAT easy, `lm_id` coerente.

* `witness_json/m_2SAT_crit_demo.json`
  ↔ `m_2SAT_crit_demo : LMetrics` (Coq)

  * 2-SAT critico, `lm_id` coerente.

Questi 6 JSON sono **allineati** con `Loventre_LMetrics_JSON_Link.v` (Coq) secondo il crosscheck.

---

### 4. Metrics bus (contratto concettuale lato Python)

A livello Python, il **metrics bus** espone almeno i seguenti campi (in sincronia con `LMetrics` Coq):

* `kappa_eff`
* `entropy_eff`
* `V0`
* `a_min`
* `p_tunnel`
* `P_success`
* `gamma_dilation`
* `time_regime`
* `mass_eff`
* `inertial_idx`
* `risk_index`
* `risk_class`
* `meta_label`
* `chi_compactness`
* `horizon_flag`

Sono gli stessi campi mappati nel documento di ponte:
`LOVENTRE_ENGINE_SYNC_COQ_v3.md`.

---

### 5. Regole operative Python (per restare allineato con Coq v3)

1. **Sempre comandi completi**

   * Prima `cd .../loventre_engine_clean_seed`, poi `python3 ...`.
   * Non lanciare mai snippet a metà senza contesto.

2. **Dopo ogni modifica alla logica del motore**

   * Eseguire sempre:

     ```bash
     python3 run_loventre_regression_suite.py
     ```
   * Se ci sono errori o mismatch, incollare l’output completo prima di toccare Coq.

3. **Non cambiare il contratto del metrics bus**

   * Qualsiasi cambiamento strutturale ai campi (aggiunta, rinomina, cambio tipo)
     → richiede:

     * aggiornamento del ponte `LOVENTRE_ENGINE_SYNC_COQ_v3.md`
     * eventuale aggiornamento dei tipi e record `LMetrics` in Coq
     * nuovo seed di stato ufficiale.

4. **Non cambiare i JSON witness canonici senza motivo fortissimo**

   * `m_seed11_cli_demo`, `m_seed_grid_demo`, `m_TSPcrit28_cli_demo`, `m_SATcrit16_cli_demo`, `m_2SAT_easy_demo`, `m_2SAT_crit_demo`
   * Se davvero serve, va:

     * aggiornato il crosscheck
     * aggiornato il lato Coq (definizioni LMetrics corrispondenti)
     * documentato nel file di stato globale (Coq e, se serve, Python).

---

### 6. Cosa farà la **nuova tab** usando questo seed

La nuova tab (ponte Python↔Coq per v4) userà **questo mini-seed** +
`MINI-SEED SYNC — PROGETTO LOVENTRE COQ` per:

* progettare evoluzioni del motore (es. SAFE_Barrier, future layer)
  **senza rompere**:

  * il regression suite Python
  * i lemmi Coq v3 già compilati;

* decidere nuove strutture condivise (SAFE_Barrier, dynamic bridge, ecc.)
  aggiornando contemporaneamente:

  * `LOVENTRE_ENGINE_SYNC_COQ_v3.md`
  * `LOVENTRE_COQ_STATE_v3_COMPILED_2025-12-09.md`.

In sintesi: questo mini-seed fotografa lo stato **Python v3 stabile** e lo rende leggibile alla tab Coq/Bridge, così che tutti i passi verso v4 (SAFE BARRIER, dynamic bridge, Main_Theorem_v4) partano da una base condivisa e documentata.

