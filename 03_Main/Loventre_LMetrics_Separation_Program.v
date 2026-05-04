(* Loventre_LMetrics_Separation_Program.v — CANON v3 *)

From Stdlib Require Import Reals.

From Loventre_Core Require Import Loventre_Core_Prelude.

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_LMetrics_Phase_Predicates.

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

(* Stub: separation statement and bridge theorem *)
Definition Loventre_LMetrics_Separation_Statement : Prop := True.

Theorem Loventre_LMetrics_Separation_Theorem_from_core_and_SAFE :
  True -> True -> Loventre_LMetrics_Separation_Statement.
Proof. intros _ _. unfold Loventre_LMetrics_Separation_Statement. exact I. Qed.
