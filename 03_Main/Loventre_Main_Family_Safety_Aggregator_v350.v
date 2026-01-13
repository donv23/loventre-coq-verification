(**
  Loventre_Main_Family_Safety_Aggregator_v350.v
  Assembla V330 (SAFE via P_accessible) + V340 (NON SAFE via NP_blackhole)
  e lo applica a 2SAT + 3SAT
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import Loventre_LMetrics_Core
                                     Loventre_LMetrics_Phase_Predicates
                                     Loventre_SAFE_Model
                                     Loventre_Class_Model
                                     Loventre_LMetrics_JSON_Witness.
From Loventre_Advanced.Geometry Require Import
       Loventre_Family_SAFE_Bridge_v330
       Loventre_Family_UNSAFE_Bridge_v340.

Module Loventre_Main_Family_Safety_Aggregator_V350.

(** Easy: P_accessible ↔ SAFE *)
Lemma TwoSAT_easy_is_SAFE :
  SAFE_condition m_2SAT_easy_demo = true.
Proof.
  apply Loventre_Family_SAFEBRIDGE_V330.Pacc_implies_SAFE.
  exact m_2SAT_easy_is_Pacc.
Qed.

Lemma ThreeSAT_demo_is_SAFE :
  SAFE_condition m_3SAT_demo = true.
Proof.
  apply Loventre_Family_SAFEBRIDGE_V330.Pacc_implies_SAFE.
  exact m_3SAT_demo_is_Pacc.
Qed.

(** Crit: NP_blackhole ↔ NOT SAFE *)
Lemma TwoSAT_crit_not_SAFE :
  SAFE_condition m_2SAT_crit_demo = false.
Proof.
  apply Loventre_Family_UNSAFEBRIDGE_V340.NPbh_implies_not_SAFE.
  exact m_2SAT_crit_is_NPbh.
Qed.

Lemma ThreeSAT_crit_not_SAFE :
  SAFE_condition m_3SAT_crit_demo = false.
Proof.
  apply Loventre_Family_UNSAFEBRIDGE_V340.NPbh_implies_not_SAFE.
  exact m_3SAT_crit_is_NPbh.
Qed.

(** Lemma riassuntivo per tutte e quattro le istanze *)
Lemma SAFE_family_summary :
  SAFE_condition m_2SAT_easy_demo = true
  /\ SAFE_condition m_3SAT_demo = true
  /\ SAFE_condition m_2SAT_crit_demo = false
  /\ SAFE_condition m_3SAT_crit_demo = false.
Proof.
  repeat split;
    try apply TwoSAT_easy_is_SAFE;
    try apply ThreeSAT_demo_is_SAFE;
    try apply TwoSAT_crit_not_SAFE;
    try apply ThreeSAT_crit_not_SAFE.
Qed.

End Loventre_Main_Family_Safety_Aggregator_V350.

