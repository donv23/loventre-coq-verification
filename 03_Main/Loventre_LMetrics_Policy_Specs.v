(* Loventre_LMetrics_Policy_Specs.v — CANON v3 *)

From Stdlib Require Import Reals Bool.
From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Policy_SAFE_Spec.

Import Loventre_Metrics_Bus.
Import Loventre_LMetrics_Phase_Predicates.Loventre_LMetrics_Phase_Predicates.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(* ----------------------------------------------------------------- *)
(* Policy decision booleana: assenza di orizzonte                    *)
(* ----------------------------------------------------------------- *)

Definition loventre_policy_decision (m : LMetrics) : bool :=
  negb (horizon_flag m).

(* ----------------------------------------------------------------- *)
(* Lemmi di onestà policy ↔ horizon                                  *)
(* ----------------------------------------------------------------- *)

Lemma policy_safe_iff_no_horizon :
  forall m : LMetrics,
    loventre_policy_decision m = true <-> horizon_flag m = false.
Proof.
  intros m. unfold loventre_policy_decision. split.
  - intro H. apply negb_true_iff in H. exact H.
  - intro H. rewrite H. reflexivity.
Qed.

Lemma policy_unsafe_iff_horizon :
  forall m : LMetrics,
    loventre_policy_decision m = false <-> horizon_flag m = true.
Proof.
  intros m. unfold loventre_policy_decision. split.
  - intro H. apply negb_false_iff in H. exact H.
  - intro H. rewrite H. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* Dalla policy alle classi di fase (con ipotesi esplicite)          *)
(* ----------------------------------------------------------------- *)

Lemma policy_safe_implies_P_like :
  forall m : LMetrics,
    loventre_policy_decision m = true ->
    ~ compact_positive m ->
    is_P_like m.
Proof.
  intros m Hpol Hncomp.
  unfold is_P_like. split.
  - exact Hncomp.
  - apply policy_safe_iff_no_horizon. exact Hpol.
Qed.

Lemma policy_unsafe_implies_NP_like_black_hole :
  forall m : LMetrics,
    loventre_policy_decision m = false ->
    compact_positive m ->
    risk_class m = risk_np_like_black_hole ->
    is_NP_like_black_hole m.
Proof.
  intros m Hpol Hcomp Hrisk.
  unfold is_NP_like_black_hole, is_NP_like, has_horizon.
  split.
  - split.
    + exact Hcomp.
    + apply policy_unsafe_iff_horizon. exact Hpol.
  - exact Hrisk.
Qed.

(* ----------------------------------------------------------------- *)
(* Loventre_Policy_Core_Program: enunciato composito                 *)
(*                                                                   *)
(* Tre componenti:                                                   *)
(*   (1) esistenza di una metrica P-like                             *)
(*   (2) esistenza di una metrica NP-like-black-hole                 *)
(*   (3) coerenza policy SAFE ⇒ colore GREEN                         *)
(*                                                                   *)
(* I primi due sono garantiti dall'assioma                           *)
(* Loventre_P_vs_NP_like_black_hole_exist_predicative                *)
(* (definito in Existence_Summary, witness dal motore Python).       *)
(* Il terzo è un teorema reale dimostrato in Policy_SAFE_Spec.       *)
(* ----------------------------------------------------------------- *)

Definition Loventre_Policy_Core_Program : Prop :=
  ((exists m : LMetrics, is_P_like m)
   /\ (exists m : LMetrics, is_NP_like_black_hole m))
  /\ policy_SAFE_implies_green_global.

Theorem Loventre_Policy_Core_Program_holds :
  Loventre_Policy_Core_Program.
Proof.
  unfold Loventre_Policy_Core_Program.
  split.
  - exact Loventre_P_vs_NP_like_black_hole_exist_predicative.
  - exact policy_SAFE_implies_green_global_proof.
Qed.
