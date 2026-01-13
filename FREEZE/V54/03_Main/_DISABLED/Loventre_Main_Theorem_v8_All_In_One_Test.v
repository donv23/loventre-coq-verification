(**
  ------------------------------------------------------------------
  Loventre_Main_Theorem_v8_All_In_One_Test.v
  Canvas 10 — Sanity test unificato su witnesses V8
  ------------------------------------------------------------------
*)

From Loventre_Main Require Import
     Loventre_Main_Theorem_v8_Prelude
     Loventre_LMetrics_v8_Aliases
     Loventre_Main_Theorem_v8_Interface
     Loventre_LMetrics_v8_SAFE
     Loventre_LMetrics_v8_Policy
     Loventre_LMetrics_v8_Risk
     Loventre_LMetrics_v8_MetaDecision.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Unset Strict Implicit.

(**
  1. Decisione locale
*)
Compute loventre_local_decision m_seed11_v8.
Compute loventre_local_decision m_TSPcrit28_v8.
Compute loventre_local_decision m_2SAT_easy_v8.
Compute loventre_local_decision m_2SAT_crit_v8.

(**
  2. Macro policy color
*)
Compute loventre_macro_policy m_seed11_v8.
Compute loventre_macro_policy m_TSPcrit28_v8.
Compute loventre_macro_policy m_2SAT_easy_v8.
Compute loventre_macro_policy m_2SAT_crit_v8.

(**
  3. Valutazione rischio
*)
Compute loventre_risk_eval m_seed11_v8.
Compute loventre_risk_eval m_TSPcrit28_v8.
Compute loventre_risk_eval m_2SAT_easy_v8.
Compute loventre_risk_eval m_2SAT_crit_v8.

(**
  4. Decisione globale aggregata
*)
Compute loventre_global_decision_v8 m_seed11_v8.
Compute loventre_global_decision_v8 m_TSPcrit28_v8.
Compute loventre_global_decision_v8 m_2SAT_easy_v8.
Compute loventre_global_decision_v8 m_2SAT_crit_v8.

(**
  Fine Canvas 10 test
*)

