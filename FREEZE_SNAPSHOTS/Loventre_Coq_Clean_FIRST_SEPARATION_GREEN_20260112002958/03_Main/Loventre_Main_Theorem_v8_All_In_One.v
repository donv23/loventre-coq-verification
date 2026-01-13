(**
  ------------------------------------------------------------------
  Loventre_Main_Theorem_v8_All_In_One.v
  Canvas 10 (Gennaio 2026)
  Unificazione nominale: SAFE + POLICY + RISK + META
  Nessuna prova formale — solo incollaggio di definizioni e wrapper.
  ------------------------------------------------------------------
*)

From Stdlib Require Import Reals.
Open Scope R_scope.

From Loventre_Main
     Require Import
       Loventre_Main_Theorem_v8_Prelude
       Loventre_LMetrics_v8_Aliases
       Loventre_LMetrics_v8_SAFE
       Loventre_LMetrics_v8_Policy
       Loventre_LMetrics_v8_Risk
       Loventre_LMetrics_v8_MetaDecision.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Unset Strict Implicit.

(**
  RICHIAMA LE QUATTRO MAPPE
  SAFE / POLICY / RISK / META
*)

Definition v8_safe_seed11   := is_P_like m_seed11_v8.
Definition v8_safe_2sat_easy := is_P_accessible m_2SAT_easy_v8.
Definition v8_safe_tspcrit  := is_black_hole_like m_TSPcrit28_v8.
Definition v8_safe_2satcrit := is_black_hole_like m_2SAT_crit_v8.

Definition v8_policy_seed11   := loventre_local_decision m_seed11_v8.
Definition v8_policy_2sat_easy := loventre_local_decision m_2SAT_easy_v8.
Definition v8_policy_tspcrit  := loventre_local_decision m_TSPcrit28_v8.
Definition v8_policy_2satcrit := loventre_local_decision m_2SAT_crit_v8.

Definition v8_risk_seed11   := loventre_risk_eval m_seed11_v8.
Definition v8_risk_2sat_easy := loventre_risk_eval m_2SAT_easy_v8.
Definition v8_risk_tspcrit  := loventre_risk_eval m_TSPcrit28_v8.
Definition v8_risk_2satcrit := loventre_risk_eval m_2SAT_crit_v8.

Definition v8_meta_seed11    := loventre_global_decision_v8 m_seed11_v8.
Definition v8_meta_2sat_easy := loventre_global_decision_v8 m_2SAT_easy_v8.
Definition v8_meta_tspcrit   := loventre_global_decision_v8 m_TSPcrit28_v8.
Definition v8_meta_2satcrit  := loventre_global_decision_v8 m_2SAT_crit_v8.

(**
  FINE FILE — INTERFACCIA TOTALE V8
*)

