(**
  ------------------------------------------------------------------
  Loventre_LMetrics_v8_MetaDecision_Test.v
  Test aggregato METADECISION — Canvas 10 (Gennaio 2026)
  ------------------------------------------------------------------
*)

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

(**
  Tutti i test sono nominali,
  solo check che la tripla sia producibile sui 4 witness canonici.
*)

Lemma MetaDecision_seed11_ok :
  exists d c r, loventre_global_decision_v8 m_seed11_v8 = (d,c,r).
Proof. repeat eexists. Qed.

Lemma MetaDecision_TSPcrit28_ok :
  exists d c r, loventre_global_decision_v8 m_TSPcrit28_v8 = (d,c,r).
Proof. repeat eexists. Qed.

Lemma MetaDecision_2SAT_easy_ok :
  exists d c r, loventre_global_decision_v8 m_2SAT_easy_v8 = (d,c,r).
Proof. repeat eexists. Qed.

Lemma MetaDecision_2SAT_crit_ok :
  exists d c r, loventre_global_decision_v8 m_2SAT_crit_v8 = (d,c,r).
Proof. repeat eexists. Qed.

(* Fine Test MetaDecision V8 *)

