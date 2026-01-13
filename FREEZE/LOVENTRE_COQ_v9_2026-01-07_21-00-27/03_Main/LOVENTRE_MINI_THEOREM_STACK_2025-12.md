# LOVENTRE_MINI_THEOREM_STACK – dicembre 2025

_Asse: LMetrics + Policy + SAFE + Profili di complessità + Witness JSON + Guardiani Python_

Root Coq:
`/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/PROGETTO TEOREMA/Loventre_Coq_Modules/Loventre_Coq_Clean`

Root Python (motore):
`/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed`

---

## 0. Compilazioni di riferimento (asse Teorema)

Geometry + Policy + SAFE + V1 + V2:

```bash
# Geometry – fasi, policy, SAFE, accessibile, complessità
"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  02_Advanced/Geometry/Loventre_LMetrics_Existence_Summary.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  02_Advanced/Geometry/Loventre_LMetrics_Phase_Predicates.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  02_Advanced/Geometry/Loventre_LMetrics_Policy_Spec.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  02_Advanced/Geometry/Loventre_LMetrics_Policy_SAFE_Spec.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  02_Advanced/Geometry/Loventre_LMetrics_Accessible_Existence.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  02_Advanced/Geometry/Loventre_LMetrics_Complexity_Profiles.v

# Main – Core Program + Teoremi V1/V2 + witness
"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  -Q 03_Main           Loventre_Main \
  03_Main/Loventre_LMetrics_Policy_Specs.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  -Q 03_Main           Loventre_Main \
  03_Main/Loventre_LMetrics_Policy_Theorem.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  -Q 03_Main           Loventre_Main \
  03_Main/Loventre_LMetrics_Separation_Program.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  -Q 03_Main           Loventre_Main \
  03_Main/Loventre_LMetrics_Witness_Separation.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  -Q 03_Main           Loventre_Main \
  03_Main/Loventre_Theorem_v1.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  -Q 03_Main           Loventre_Main \
  03_Main/Loventre_Theorem_v1_Corollaries.v

"/Applications/Coq-Platform~8.18~2023.11.app/Contents/Resources/bin/coqc" \
  -Q 02_Advanced/Geometry Loventre_Geometry \
  -Q 03_Main           Loventre_Main \
  03_Main/Loventre_Theorem_v2_Sketch.v

