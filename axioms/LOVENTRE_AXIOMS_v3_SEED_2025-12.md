# LOVENTRE — AXIOMS v3 (Dicembre 2025)

## 0. Scopo del seed

Questo seed descrive, in linguaggio umano, gli **assiomi principali** del modello
Loventre v3/v3+ così come compaiono nei file Coq (Dicembre 2025), con particolare
attenzione a:

- esistenza di profili P_like_accessible (P_accessible);
- ruolo del seed_grid come riferimento P_accessible canonico;
- ruolo del candidato `m_P_like_accessible_candidate`;
- meta-label dei witness sperimentali 2-SAT (easy / crit).

Tutto quello che segue è il gemello testuale del file:

- `03_Main/Loventre_Axioms_v3_Summary.v`

Questo seed **non introduce nuove ipotesi**: si limita a spiegare e
riorganizzare quelle già presenti in Coq.

---

## 1. Axioma centrale su P_like_accessible

### 1.1. Forma Coq

Nel modulo Geometry:

- `02_Advanced/Geometry/Loventre_LMetrics_Accessible_Existence.v`

compaiono:

```coq
Parameter LMetrics : Type.
Parameter is_P_like_accessible : LMetrics -> Prop.

Axiom exists_P_like_accessible :
  exists m : LMetrics, is_P_like_accessible m.

