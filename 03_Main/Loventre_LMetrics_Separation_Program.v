(* Loventre_LMetrics_Separation_Program.v — CANON v3 *)

From Stdlib Require Import Reals.

From Loventre_Core Require Import Loventre_Core_Prelude.

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Policy_SAFE_Spec.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Metrics_Bus.
Import Loventre_LMetrics_Phase_Predicates.Loventre_LMetrics_Phase_Predicates.

Lemma Loventre_Safe_vs_NP_like_black_hole_separated :
  forall (m : LMetrics),
    loventre_policy_decision m = true ->
    ~(loventre_policy_decision m = false).
Proof.
  intros m Hs Hcontra.
  rewrite Hs in Hcontra. discriminate.
Qed.

Lemma Loventre_Safe_implies_P_like :
  forall (m : LMetrics),
    loventre_policy_decision m = true ->
    ~ compact_positive m ->
    is_P_like m.
Proof.
  intros m Hs Hncomp.
  apply policy_safe_implies_P_like; assumption.
Qed.

Lemma Loventre_Unsafe_implies_NP_like_black_hole :
  forall (m : LMetrics),
    loventre_policy_decision m = false ->
    compact_positive m ->
    risk_class m = risk_np_like_black_hole ->
    is_NP_like_black_hole m.
Proof.
  intros m Hu Hcomp Hrisk.
  apply policy_unsafe_implies_NP_like_black_hole; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(* Separation statement: la coerenza policy + SAFE→GREEN implica    *)
(* l'esistenza di entrambe le classi (P-like e NP-like-BH).         *)
(* ----------------------------------------------------------------- *)

Definition Loventre_LMetrics_Separation_Statement : Prop :=
  (exists m : LMetrics, is_P_like m)
  /\ (exists m : LMetrics, is_NP_like_black_hole m).

Theorem Loventre_LMetrics_Separation_Theorem_from_core_and_SAFE :
  Loventre_Policy_Core_Program ->
  policy_SAFE_implies_green_global ->
  Loventre_LMetrics_Separation_Statement.
Proof.
  intros Hcore _Hsafe.
  unfold Loventre_LMetrics_Separation_Statement.
  unfold Loventre_Policy_Core_Program in Hcore.
  destruct Hcore as [Hexist _].
  exact Hexist.
Qed.
