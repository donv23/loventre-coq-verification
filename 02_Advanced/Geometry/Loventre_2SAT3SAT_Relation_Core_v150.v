(** ====================================================== *)
(** Loventre 2SAT–3SAT Relation Core — v150                *)
(** Geometry layer only — no 03_Main dependencies          *)
(** ====================================================== *)

From Loventre_Core      Require Import Loventre_Core_Prelude.
From Loventre_Advanced   Require Import
     Loventre_LMetrics_Core
     Loventre_LMetrics_Phase_Predicates
     Loventre_Metrics_Bus
     Loventre_SAFE_Model
     Loventre_Class_Model.

From Loventre_Advanced.Geometry Require Import
     Loventre_2SAT_LMetrics_From_JSON
     Loventre_2SAT_EasyCrit_Compare
     Loventre_3SAT_LMetrics_From_JSON
     Loventre_3SAT_EasyCrit_Compare
     Loventre_3SAT_SAFE_Local_v122
     Loventre_3SAT_Class_Local_v123.

(** ------------------------------------------------------ *)
(**  Core relation: easy profiles sit in same SAFE sector   *)
(** ------------------------------------------------------ *)

Lemma easy_2SAT_implies_easy_3SAT_Pacc :
  In_Pacc_Lov m_2SAT_easy_demo ->
  In_Pacc_Lov m_3SAT_easy_demo.
Proof.
  intros H2.
  apply easy_3SAT_is_Pacc.
Qed.

(** ------------------------------------------------------ *)
(**  Crit relation: crit profiles remain outside SAFE/Pacc  *)
(** ------------------------------------------------------ *)

Lemma crit_2SAT_implies_crit_3SAT_NPbh :
  In_NPbh_Lov m_2SAT_crit_demo ->
  In_NPbh_Lov m_3SAT_crit_demo.
Proof.
  intros Hc.
  apply crit_3SAT_is_NPbh.
Qed.

(** ------------------------------------------------------ *)
(**  Backbone — no intersection Pacc vs NPbh                *)
(** ------------------------------------------------------ *)

Lemma no_collapse_2SAT3SAT_easy_crit :
  forall m,
    In_Pacc_Lov m_2SAT_easy_demo /\
    In_NPbh_Lov m_3SAT_crit_demo ->
    False.
Proof.
  intros m [Hp Hc].
  exact (in_Pacc_Lov_vs_in_NPbh_Lov_contra Hp Hc).
Qed.

(** ------------------------------------------------------ *)
(** END v150 Core                                           *)
(** ------------------------------------------------------ *)

