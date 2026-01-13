# LOVENTRE_THEOREM_V2_SKETCH – Seed (dicembre 2025)

_Asse LMetrics + Policy + SAFE + Profili di complessità_

Root Coq:
`/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/PROGETTO TEOREMA/Loventre_Coq_Modules/Loventre_Coq_Clean`

File Geometry rilevanti:

- `02_Advanced/Geometry/Loventre_LMetrics_Existence_Summary.v`
- `02_Advanced/Geometry/Loventre_LMetrics_Phase_Predicates.v`
- `02_Advanced/Geometry/Loventre_LMetrics_Policy_Spec.v`
- `02_Advanced/Geometry/Loventre_LMetrics_Policy_SAFE_Spec.v`
- `02_Advanced/Geometry/Loventre_LMetrics_Accessible_Existence.v`
- `02_Advanced/Geometry/Loventre_LMetrics_Complexity_Profiles.v`

File Main rilevanti:

- `03_Main/Loventre_LMetrics_Policy_Specs.v`
- `03_Main/Loventre_LMetrics_Policy_Theorem.v`
- `03_Main/Loventre_LMetrics_Separation_Program.v`
- `03_Main/Loventre_LMetrics_Witness_Separation.v`
- `03_Main/Loventre_Theorem_v1.v`
- `03_Main/Loventre_Theorem_v1_Corollaries.v`
- `03_Main/Loventre_Theorem_v2_Sketch.v`

Compilazione di riferimento:

```bash
"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  -Q 03_Main           Loventre_Main \
  03_Main/Loventre_Theorem_v2_Sketch.v

