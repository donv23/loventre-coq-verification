(** ====================================================== *)
(** Loventre 2SAT–3SAT Class Bridge — v150                  *)
(** Re-express global map via class predicates              *)
(** ====================================================== *)

From Loventre_Core Require Import Loventre_Core_Prelude.

From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_Metrics_Bus
     Loventre_LMetrics_Phase_Predicates
     Loventre_Class_Model.

From Loventre_Advanced.Geometry Require Import
     Loventre_2SAT_LMetrics_From_JSON
     Loventre_3SAT_LMetrics_From_JSON
     Loventre_2SAT3SAT_Relation_Global_v150.

(** ------------------------------------------------------ *)
(** Easy: P-accessible class bridge                         *)
(** ------------------------------------------------------ *)

Lemma class_bridge_easy_bool :
  is_Pacc m_2SAT_easy_demo = true ->
  is_Pacc m_3SAT_easy_demo = true.
Proof.
  intros H.
  apply map_global_easy_preserves_Pacc.
  unfold In_Pacc_Lov.
  exact H.
Qed.

(** ------------------------------------------------------ *)
(** Crit: NP-blackhole class bridge                         *)
(** ------------------------------------------------------ *)

Lemma class_bridge_crit_bool :
  is_NP_bh m_2SAT_crit_demo = true ->
  is_NP_bh m_3SAT_crit_demo = true.
Proof.
  intros H.
  apply map_global_crit_preserves_NPbh.
  unfold In_NP_bh_Lov.
  exact H.
Qed.

(** ------------------------------------------------------ *)
(** Unified statement                                       *)
(** ------------------------------------------------------ *)

Lemma class_bridge_easy_or_crit :
  (is_Pacc m_2SAT_easy_demo = true ->
   is_Pacc m_3SAT_easy_demo = true)
/\ (is_NP_bh m_2SAT_crit_demo = true ->
    is_NP_bh m_3SAT_crit_demo = true).
Proof.
  split.
  - apply class_bridge_easy_bool.
  - apply class_bridge_crit_bool.
Qed.

(** ------------------------------------------------------ *)
(** END v150 Class Bridge                                   *)
(** ------------------------------------------------------ *)

