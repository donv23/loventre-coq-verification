(******************************************************************************)
(*  Loventre_LMetrics_Accessible_Existence.v                                  *)
(*  Triple existence P, P_acc, NP-like-BH                                     *)
(******************************************************************************)

From Stdlib Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Phase_Predicates.

Import Loventre_Metrics_Bus.
Import Loventre_LMetrics_Phase_Predicates.Loventre_LMetrics_Phase_Predicates.

Axiom exists_P_like_accessible :
  exists m : LMetrics, is_P_like_accessible m.

Definition Loventre_P_Paccessible_NP_like_triple_exist : Prop :=
  (exists m : LMetrics, Loventre_LMetrics_Existence_Summary.is_P_like m)
  /\ (exists m : LMetrics, is_P_like_accessible m)
  /\ (exists m : LMetrics, Loventre_LMetrics_Existence_Summary.is_NP_like_black_hole m).

Lemma Loventre_P_Paccessible_NP_like_triple_exist_true :
  Loventre_P_Paccessible_NP_like_triple_exist.
Proof.
  unfold Loventre_P_Paccessible_NP_like_triple_exist.
  split.
  - exact (ex_intro _ _ m_seed11_soddisfa_is_P_like).
  - split.
    + exact exists_P_like_accessible.
    + exact (ex_intro _ _ m_TSPcrit28_soddisfa_is_NP_like_black_hole).
Qed.

Theorem Loventre_P_Paccessible_NP_like_triple_exist_from_core :
  Loventre_P_Paccessible_NP_like_triple_exist.
Proof.
  apply Loventre_P_Paccessible_NP_like_triple_exist_true.
Qed.
