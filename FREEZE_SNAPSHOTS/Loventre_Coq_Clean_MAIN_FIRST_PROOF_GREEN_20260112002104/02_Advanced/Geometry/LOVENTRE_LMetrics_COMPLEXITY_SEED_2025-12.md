# LOVENTRE_LMetrics_COMPLEXITY_SEED – dicembre 2025

_Asse Geometry: profili di complessità su LMetrics + witness concreti_

Root Coq:
`/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/PROGETTO TEOREMA/Loventre_Coq_Modules/Loventre_Coq_Clean`

File Geometry coinvolti:

- `02_Advanced/Geometry/Loventre_LMetrics_Existence_Summary.v`
- `02_Advanced/Geometry/Loventre_LMetrics_Phase_Predicates.v`
- `02_Advanced/Geometry/Loventre_LMetrics_Complexity_Profiles.v`
- `02_Advanced/Geometry/Loventre_LMetrics_Complexity_Witness.v`

Questo seed fotografa lo stato di dicembre 2025 per la parte:

> LMetrics + Profili di “complessità” P_like / NP_like-critico  
> + loro aggancio ai witness concreti (seed11, TSPcrit28, SATcrit16).

---

## 1. Predicati astratti su LMetrics (richiamo)

Da:

- `Loventre_LMetrics_Existence_Summary.v`
- `Loventre_LMetrics_Phase_Predicates.v`

abbiamo i predicati astratti sulle fasi:

- `is_P_like : LMetrics -> Prop`
- `is_NP_like_black_hole : LMetrics -> Prop`

più il vocabolario di fase:

- `is_low_risk : LMetrics -> Prop`  
  ↔ `risk_class m = risk_LOW`

- `is_black_hole : LMetrics -> Prop`  
  ↔ `horizon_flag m = true`

- `is_non_black_hole : LMetrics -> Prop`  
  ↔ `horizon_flag m = false`

e la fase P_like accessibile / borderline verde:

```coq
Definition is_P_like_accessible (m : LMetrics) : Prop :=
  is_low_risk m /\
  is_non_black_hole m /\
  loventre_global_decision m = GD_borderline /\
  loventre_global_color m = GC_green.

