(**
  Loventre_Main_Family_Complete_Test_v370.v
  Verifica globale SAFE <-> classe per tutti i witness
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_LMetrics_Phase_Predicates
     Loventre_SAFE_Model
     Loventre_Class_Model
     Loventre_LMetrics_JSON_Witness.
From Loventre_Advanced.Geometry Require Import
     Loventre_Family_SAFE_Bridge_v330
     Loventre_Family_UNSAFE_Bridge_v340.
From Loventre_Main Require Import
     Loventre_Main_Family_Class_Safe_Bridge_v360.

Module Loventre_Main_Family_Complete_Test_V370.

(** --- Direzioni già dimostrate (V330, V340, V360) --- *)
Lemma SAFE_true_for_easy_2SAT :
  SAFE_condition m_2SAT_easy_demo = true.
Proof. apply TwoSAT_easy_is_SAFE. Qed.

Lemma SAFE_true_for_demo_3SAT :
  SAFE_condition m_3SAT_demo = true.
Proof. apply ThreeSAT_demo_is_SAFE. Qed.

Lemma SAFE_false_for_crit_2SAT :
  SAFE_condition m_2SAT_crit_demo = false.
Proof. apply TwoSAT_crit_not_SAFE. Qed.

Lemma SAFE_false_for_crit_3SAT :
  SAFE_condition m_3SAT_crit_demo = false.
Proof. apply ThreeSAT_crit_not_SAFE. Qed.

(** --- familiari: SAFE -> classe --- *)
Lemma SAFE_implies_class_for_all :
   (is_P_accessible m_2SAT_easy_demo = true)
 /\ (is_P_accessible m_3SAT_demo = true)
 /\ (is_NP_blackhole m_2SAT_crit_demo = true)
 /\ (is_NP_blackhole m_3SAT_crit_demo = true).
Proof.
  split.
  - apply m_2SAT_easy_is_Pacc.
  split.
  - apply m_3SAT_demo_is_Pacc.
  split.
  - apply m_2SAT_crit_is_NPbh.
  - apply m_3SAT_crit_is_NPbh.
Qed.

(** --- class -> SAFE --- *)
Lemma class_implies_SAFE_for_all :
   (SAFE_condition m_2SAT_easy_demo = true)
 /\ (SAFE_condition m_3SAT_demo = true)
 /\ (SAFE_condition m_2SAT_crit_demo = false)
 /\ (SAFE_condition m_3SAT_crit_demo = false).
Proof.
  split.
  - apply TwoSAT_easy_is_SAFE.
  split.
  - apply ThreeSAT_demo_is_SAFE.
  split.
  - apply TwoSAT_crit_not_SAFE.
  - apply ThreeSAT_crit_not_SAFE.
Qed.

(** --- Big theorem: SAFE <-> CLASS family-wide --- *)
Lemma Family_FULL_characterization :
     (SAFE_condition m_2SAT_easy_demo = true
      <-> is_P_accessible m_2SAT_easy_demo = true)
  /\ (SAFE_condition m_3SAT_demo = true
      <-> is_P_accessible m_3SAT_demo = true)
  /\ (SAFE_condition m_2SAT_crit_demo = false
      <-> is_NP_blackhole m_2SAT_crit_demo = true)
  /\ (SAFE_condition m_3SAT_crit_demo = false
      <-> is_NP_blackhole m_3SAT_crit_demo = true).
Proof.
  apply Loventre_Main_Family_Class_Safe_Bridge_V360.Family_roundtrip_summary.
Qed.

End Loventre_Main_Family_Complete_Test_V370.

