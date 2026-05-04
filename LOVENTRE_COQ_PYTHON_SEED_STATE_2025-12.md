# LOVENTRE – SEED DI STATO COQ + PYTHON
(Dicembre 2025 – ponte vivo tra motore e formalizzazione)

## 0. Scopo di questo seed

Questo documento serve come foto di stato del progetto Loventre nella versione Coq + Python a dicembre 2025, pensata per:

- spiegare da dove veniamo (storia breve del progetto e del motore Python),
- fissare lo stato attuale della parte Coq (moduli, lemma, convenzioni),
- chiarire le regole di lavoro tra l’utente (Vincenzo) e l’assistente (GPT),
- indicare la direzione futura (roadmap concettuale, non dettagli operativi).

È scritto per essere letto da:

- me stesso in futuro (Vincenzo),
- una “nuova te” (nuova istanza dell’assistente) che entra nel progetto senza contesto.

---

## 1. Da dove veniamo

### 1.1 Progetto Loventre (visione generale)

Esiste da anni un’idea di Teorema di Loventre, legata a:

- separazione strutturale tra P-like e NP-like critico,
- vista attraverso curvatura informazionale, barriere di potenziale, regimi critici,
- collegamento concettuale con immagini fisiche (massa, orizzonte, black hole, ecc.).

Il progetto è diviso in due grandi blocchi:

### Loventre Engine Python

Un motore operativo, euristico, “proprietario”, che:

- prende istanze (SAT, TSP, ecc.),
- calcola un insieme di metriche (curvatura, entropia, compattessa, ecc.),
- costruisce un bus metrico (`metrics` dict),
- passa tutto attraverso un **Policy Bridge** che decide:

  - `INSISTI` / `VALUTA` / `RITIRA` e  
  - `safe` / `borderline` / `critical`.

### Loventre_Coq_Clean

Un progetto Coq che formalizza:

- il bus metrico tipato `LMetrics`,
- i predicati critici (`SAT_crit`, `TSP_crit`, `Metrics_witness`),
- le decisioni qualitative (`GlobalDecision`, `GlobalColor`),
- e in prospettiva il Teorema di Loventre vero e proprio.

L’idea centrale:

- il motore Python **produce istanze concrete**;
- la parte Coq ne **cattura la struttura logica e le congetture**.

---

## 2. Ruolo del motore Python (snapshot)

Lato Python (cartella `loventre_engine_clean_seed`) abbiamo:

- Un **Loventre Metrics Bus** in forma di `dict metrics` con chiavi tipo:

  - `kappa_eff`, `entropy_eff`, `V0`, `a_min`,
  - `p_tunnel`, `P_success`,
  - `gamma_dilation`, `time_regime`,
  - `mass_eff`, `inertial_idx`,
  - `risk_index`, `risk_class`, `meta_label`,
  - `chi_compactness`, `horizon_flag`,
  - blocco `loventre_global` (decisione operativa `INSISTI` / `VALUTA` / `RITIRA` + colore),

  più campi del **Policy Bridge**:

  - `global_decision_label ∈ {safe, borderline, critical, invalid}`,
  - `global_decision_score ∈ [0,1]`,
  - `global_meta_explanation` (stringa compatta).

- Un **Policy Bridge** (`loventre_policy_bridge.py`) che:

  - legge `risk_class`, `risk_index`, `p_tunnel`, `horizon_flag`, `loventre_global`,
  - produce una decisione strutturale `safe` / `borderline` / `critical` / `invalid`,
  - scrive il risultato nel bus `metrics`.

- Una **pipeline JSON → Coq**:

  Esistono JSON di tipo LMetrics-like, ad esempio:

  - `lmetrics_TSP_crit28_example.json`,
  - `lmetrics_SAT_crit16_example.json`,

  che vengono trasformati in snippet Coq del tipo:

  ```coq
  Definition m_TSPcrit28_json : LMetrics := {| ... |}.
  Definition m_SATcrit16_json : LMetrics := {| ... |}.

