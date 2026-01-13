(** ====================================================== *)
(** Loventre 2SAT–3SAT Easy Map — v150                     *)
(** Geometry layer only — SAFE/Pacc mapping                *)
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
     Loventre_3SAT_Class_Local_v123.

(** ------------------------------------------------------ *)
(**  Profile-level mapping: 2SAT_easy ⇒ 3SAT_easy           *)
(** ------------------------------------------------------ *)

Lemma map_easy_kappa :
  m_2SAT_easy_demo.(kappa_eff) = m_3SAT_easy_demo.(kappa_eff).
Proof. reflexivity. Qed.

Lemma map_easy_entropy :
  m_2SAT_easy_demo.(entropy_eff) = m_3SAT_easy_demo.(entropy_eff).
Proof. reflexivity. Qed.

Lemma map_easy_barrier :
  m_2SAT_easy_demo.(V0) = m_3SAT_easy_demo.(V0).
Proof. reflexivity. Qed.

Lemma map_easy_tunnel :
  m_2SAT_easy_demo.(p_tunnel) = m_3SAT_easy_demo.(p_tunnel).
Proof. reflexivity. Qed.

(** ------------------------------------------------------ *)
(**  Semantic: Pacc is preserved via equal metrics           *)
(** ------------------------------------------------------ *)

Lemma easy_maps_preserve_Pacc :
  In_Pacc_Lov m_2SAT_easy_demo ->
  In_Pacc_Lov m_3SAT_easy_demo.
Proof.
  intros H.
  apply easy_3SAT_is_Pacc.
Qed.

(** ------------------------------------------------------ *)
(** END v150 Easy Map                                       *)
(** ------------------------------------------------------ *)

