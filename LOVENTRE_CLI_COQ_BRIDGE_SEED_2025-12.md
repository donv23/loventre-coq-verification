# LOVENTRE CLI → COQ BRIDGE – SEED DI STATO (Dicembre 2025)

## 0. Scopo

Questo seed documenta la **pipeline operativa** che collega:

- un file `metrics_X.json` lato Loventre Engine (Python),
- il **Loventre Policy Bridge** (decisione globale qualitativa),
- la proiezione in un **bus LMetrics** compatibile con Coq,
- una **snippet Coq** `Definition m_X : LMetrics := ...` pronta da copiare
  nel progetto `Loventre_Coq_Clean`.

Il tutto è incapsulato in una **mini–CLI**:

- `loventre_metrics_cli_coq_bridge.py`

che realizza il ponte Python → Coq in un colpo solo.

---

## 1. Posizione nell’architettura del motore

Componenti coinvolti:

1. `loventre_policy_bridge.py`
   - implementa il **Policy Bridge**:
     - `loventre_local_decision(...)`
     - `apply_policy_bridge_to_metrics(metrics)`
     - `append_policy_bridge_to_metrics(metrics)`
   - arricchisce un `metrics: dict` con chiavi:
     - `global_decision_label` (safe / borderline / critical / invalid),
     - `global_decision_score` (scala [0,1]),
     - `global_meta_explanation` (stringa sintetica),
     - lasciando intatto il blocco motore `metrics["loventre_global"]`
       (INSISTI/VALUTA/RITIRA + GREEN/AMBER/RED + global_score).

2. `loventre_project_metrics_to_lmetrics.py`
   - proietta un `metrics: dict` in un **LMetrics-like dict**:
     - seleziona e rinomina i campi rilevanti:
       - `kappa_eff`, `entropy_eff`, `V0`, `a_min`,
       - `p_tunnel`, `P_success`,
       - `gamma_dilation`, `time_regime`,
       - `mass_eff`, `inertial_idx`,
       - `risk_index`, `risk_class`,
       - `meta_label`,
       - `chi_compactness`, `horizon_flag`,
       - `loventre_global_decision`, `loventre_global_color`,
       - `loventre_global_score`.
   - questo dict è la controparte JSON del record `LMetrics` in Coq.

3. `loventre_lmetrics_to_coq_snippet.py`
   - prende un JSON `lmetrics_X.json` e produce su stdout una snippet Coq:
     - `Definition m_X : LMetrics := {| ... |}.`
   - usa un ordine di campi `FIELDS_ORDER` stabile e una mappatura
     `coq_of_field` che:
     - trasforma stringhe Python `"NP_like_black_hole"` in costruttori Coq
       `risk_NP_like_black_hole`,
     - mappa `"GD_safe"`, `"GC_green"`, ecc. nei corrispondenti
       costruttori Coq (`GD_safe`, `GC_green`, ...),
     - lascia alcuni campi come `_ (* TODO: fill *)` quando non sono presenti
       nel JSON di partenza (es. kappa_eff, entropy_eff in alcuni metrics demo).

4. `loventre_metrics_cli_coq_bridge.py` (nuovo)
   - è la CLI di alto livello che orchestra il tutto.

---

## 2. CLI unica: `loventre_metrics_cli_coq_bridge.py`

### 2.1 API e uso

Script:

```bash
python3 loventre_metrics_cli_coq_bridge.py \
  --metrics-json metrics_X.json \
  --def-name m_X_json

