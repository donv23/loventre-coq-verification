(** ====================================================== *)
(** Loventre 2SAT–3SAT Mini Theorem — v160                 *)
(** End-to-end class preservation for canonical witnesses  *)
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
     Loventre_2SAT3SAT_Class_Bridge_v150.

(** ------------------------------------------------------ *)
(** Mini Theorem: P-accessible preservation                *)
(** ------------------------------------------------------ *)

Lemma mini_theorem_2SAT3SAT_easy :
  is_Pacc m_2SAT_easy_demo = true ->
  is_Pacc m_3SAT_easy_demo = true.
Proof.
  intro H.
  apply class_bridge_easy_bool.
  exact H.
Qed.

(** ------------------------------------------------------ *)
(** Mini Theorem: NP-blackhole preservation                *)
(** ------------------------------------------------------ *)

Lemma mini_theorem_2SAT3SAT_crit :
  is_NP_bh m_2SAT_crit_demo = true ->
  is_NP_bh m_3SAT_crit_demo = true.
Proof.
  intro H.
  apply class_bridge_crit_bool.
  exact H.
Qed.

(** ------------------------------------------------------ *)
(** Unified end-to-end result                              *)
(** ------------------------------------------------------ *)

Theorem mini_theorem_2SAT3SAT_end_to_end :
  (is_Pacc m_2SAT_easy_demo = true ->
   is_Pacc m_3SAT_easy_demo = true)
/\ (is_NP_bh m_2SAT_crit_demo = true ->
    is_NP_bh m_3SAT_crit_demo = true).
Proof.
  split.
  - apply mini_theorem_2SAT3SAT_easy.
  - apply mini_theorem_2SAT3SAT_crit.
Qed.

(** ------------------------------------------------------ *)
(** END v160 Mini Theorem                                   *)
(** ------------------------------------------------------ *)

