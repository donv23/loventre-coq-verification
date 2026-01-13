(**
  ------------------------------------------------------------------
  Loventre_LMetrics_v8_Policy_Test.v
  Test nominali del Policy Layer V8 — Canvas 9 (Gennaio 2026)
  ------------------------------------------------------------------
*)

From Stdlib Require Import Reals.
Open Scope R_scope.

From Loventre_Main
     Require Import
       Loventre_Main_Theorem_v8_Prelude
       Loventre_LMetrics_v8_Aliases
       Loventre_LMetrics_v8_Policy.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

(**
  1. Test locali sul decision algorithm
*)

Lemma policy_seed11 :
  loventre_local_decision m_seed11_v8 = INSISTI \/
  loventre_local_decision m_seed11_v8 = VALUTA \/
  loventre_local_decision m_seed11_v8 = RITIRA.
Proof. all: unfold loventre_local_decision; destruct (Rlt_dec _ _); auto. Qed.

Lemma policy_TSPcrit28 :
  loventre_local_decision m_TSPcrit28_v8 = INSISTI \/
  loventre_local_decision m_TSPcrit28_v8 = VALUTA \/
  loventre_local_decision m_TSPcrit28_v8 = RITIRA.
Proof. all: unfold loventre_local_decision; destruct (Rlt_dec _ _); auto. Qed.

(**
  2. Test sulla macro-policy
*)

Lemma macro_seed11_color :
  loventre_macro_policy m_seed11_v8 = GREEN \/
  loventre_macro_policy m_seed11_v8 = AMBER \/
  loventre_macro_policy m_seed11_v8 = RED.
Proof.
  unfold loventre_macro_policy; destruct (loventre_local_decision _); auto.
Qed.

Lemma macro_TSPcrit28_color :
  loventre_macro_policy m_TSPcrit28_v8 = GREEN \/
  loventre_macro_policy m_TSPcrit28_v8 = AMBER \/
  loventre_macro_policy m_TSPcrit28_v8 = RED.
Proof.
  unfold loventre_macro_policy; destruct (loventre_local_decision _); auto.
Qed.

(**
  3. Risk evaluation sanity
*)

Lemma risk_seed11 :
  loventre_risk_eval m_seed11_v8 = RISK_LOW \/
  loventre_risk_eval m_seed11_v8 = RISK_MEDIUM \/
  loventre_risk_eval m_seed11_v8 = RISK_HIGH.
Proof.
  unfold loventre_risk_eval, loventre_macro_policy;
  destruct (loventre_local_decision _); auto.
Qed.

Lemma risk_TSPcrit28 :
  loventre_risk_eval m_TSPcrit28_v8 = RISK_LOW \/
  loventre_risk_eval m_TSPcrit28_v8 = RISK_MEDIUM \/
  loventre_risk_eval m_TSPcrit28_v8 = RISK_HIGH.
Proof.
  unfold loventre_risk_eval, loventre_macro_policy;
  destruct (loventre_local_decision _); auto.
Qed.

(**
  ------------------------------------------------------------------
  Fine test Policy Canvas 9
  ------------------------------------------------------------------
*)

