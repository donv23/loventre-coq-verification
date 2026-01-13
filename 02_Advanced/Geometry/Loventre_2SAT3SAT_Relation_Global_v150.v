(** ====================================================== *)
(** Loventre 2SAT–3SAT Global Relation — v150               *)
(** Geometry layer aggregator                               *)
(** Easy ⇒ Easy (Pacc),  Crit ⇒ Crit (NP_blackhole)         *)
(** ====================================================== *)

From Loventre_Core      Require Import Loventre_Core_Prelude.
From Loventre_Advanced   Require Import
     Loventre_LMetrics_Core
     Loventre_Metrics_Bus
     Loventre_LMetrics_Phase_Predicates
     Loventre_SAFE_Model
     Loventre_Class_Model.

From Loventre_Advanced.Geometry Require Import
     Loventre_2SAT_LMetrics_From_JSON
     Loventre_2SAT_EasyCrit_Compare
     Loventre_3SAT_LMetrics_From_JSON
     Loventre_3SAT_EasyCrit_Compare
     Loventre_3SAT_SAFE_Local_v122
     Loventre_3SAT_Class_Local_v123
     Loventre_2SAT3SAT_Relation_Easy_Map_v150
     Loventre_2SAT3SAT_Relation_Crit_Map_v150.

(** ------------------------------------------------------ *)
(** EASY: P-accessible preservation                         *)
(** ------------------------------------------------------ *)

Lemma map_global_easy_preserves_Pacc :
  In_Pacc_Lov m_2SAT_easy_demo ->
  In_Pacc_Lov m_3SAT_easy_demo.
Proof.
  intros H.
  apply easy_maps_preserve_Pacc; exact H.
Qed.

(** ------------------------------------------------------ *)
(** CRIT: NP-blackhole preservation                         *)
(** ------------------------------------------------------ *)

Lemma map_global_crit_preserves_NPbh :
  In_NP_bh_Lov m_2SAT_crit_demo ->
  In_NP_bh_Lov m_3SAT_crit_demo.
Proof.
  intros H.
  apply crit_maps_preserve_NPbh; exact H.
Qed.

(** ------------------------------------------------------ *)
(** Combined statement: structural preservation             *)
(** ------------------------------------------------------ *)

Lemma map_global_Pacc_or_NPbh :
  (In_Pacc_Lov m_2SAT_easy_demo ->
   In_Pacc_Lov m_3SAT_easy_demo)
/\ (In_NP_bh_Lov m_2SAT_crit_demo ->
    In_NP_bh_Lov m_3SAT_crit_demo).
Proof.
  split.
  - apply map_global_easy_preserves_Pacc.
  - apply map_global_crit_preserves_NPbh.
Qed.

(** ------------------------------------------------------ *)
(** END v150 Global Relation                                *)
(** ------------------------------------------------------ *)

