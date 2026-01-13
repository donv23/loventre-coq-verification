(** ====================================================== *)
(** Loventre 2SAT–3SAT Critical Map — v150                  *)
(** Geometry layer only — NP_blackhole mapping              *)
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
(**  Profile-level mapping: 2SAT_crit ⇒ 3SAT_crit            *)
(** ------------------------------------------------------ *)

Lemma map_crit_kappa :
  m_2SAT_crit_demo.(kappa_eff) = m_3SAT_crit_demo.(kappa_eff).
Proof. reflexivity. Qed.

Lemma map_crit_entropy :
  m_2SAT_crit_demo.(entropy_eff) = m_3SAT_crit_demo.(entropy_eff).
Proof. reflexivity. Qed.

Lemma map_crit_barrier :
  m_2SAT_crit_demo.(V0) = m_3SAT_crit_demo.(V0).
Proof. reflexivity. Qed.

Lemma map_crit_tunnel :
  m_2SAT_crit_demo.(p_tunnel) = m_3SAT_crit_demo.(p_tunnel).
Proof. reflexivity. Qed.

(** ------------------------------------------------------ *)
(**  Semantic: NP_blackhole is preserved via equal metrics   *)
(** ------------------------------------------------------ *)

Lemma crit_maps_preserve_NPbh :
  In_NP_bh_Lov m_2SAT_crit_demo ->
  In_NP_bh_Lov m_3SAT_crit_demo.
Proof.
  intros H.
  apply crit_3SAT_is_NP_bh.
Qed.

(** ------------------------------------------------------ *)
(** END v150 Critical Map                                   *)
(** ------------------------------------------------------ *)

