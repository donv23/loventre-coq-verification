(******************************************************************************)
(*                                                                            *)
(*  Loventre_LMetrics_Accessible_Existence.v (03_Main)                        *)
(*                                                                            *)
(*   Triple existence P, P_acc, NP-like-BH                                    *)
(*                                                                            *)
(******************************************************************************)

From Coq Require Import Reals.

From Loventre_Main Require Import
  Loventre_LMetrics_Existence_Summary.

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Phase_Predicates.

(******************************************************************************)
(*  Assioma: esistenza P_accessible                                           *)
(******************************************************************************)

Axiom exists_P_like_accessible :
  exists m : LMetrics, is_P_like_accessible m.

(******************************************************************************)
(*  Tripla definizione                                                        *)
(******************************************************************************)

Definition Loventre_P_Paccessible_NP_like_triple_exist : Prop :=
  (exists m : LMetrics, is_P_like m)
  /\ (exists m : LMetrics, is_P_like_accessible m)
  /\ (exists m : LMetrics, is_NP_like_black_hole m).

(******************************************************************************)
(*  Lemma: tripla esistenza                                                   *)
(******************************************************************************)

Lemma Loventre_P_Paccessible_NP_like_triple_exist_true :
  Loventre_P_Paccessible_NP_like_triple_exist.
Proof.
  unfold Loventre_P_Paccessible_NP_like_triple_exist.
  split.

  - destruct Loventre_P_vs_NP_like_black_hole_exist_predicative as [H _].
    exact H.

  - split.
    + exact exists_P_like_accessible.
    + destruct Loventre_P_vs_NP_like_black_hole_exist_predicative as [_ H].
      exact H.
Qed.

(******************************************************************************)
(*  Theorem di facciata                                                       *)
(******************************************************************************)

Theorem Loventre_P_Paccessible_NP_like_triple_exist_from_core :
  Loventre_P_Paccessible_NP_like_triple_exist.
Proof.
  apply Loventre_P_Paccessible_NP_like_triple_exist_true.
Qed.

