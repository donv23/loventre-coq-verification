(* ====================================================================== *)
(* Loventre_LMetrics_Separation_Program.v                                 *)
(*                                                                       *)
(* Primo lemma costruttivo di separazione: SAFE vs NP-like-black-hole.   *)
(* Layer: 03_Main (canonico v3)                                          *)
(* ====================================================================== *)

From Stdlib Require Import Reals.

From Loventre_Core Require Import
  Loventre_Core_Prelude.

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_Predicates.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Metrics_Bus.
Import Loventre_LMetrics_Phase_Predicates.
Import Loventre_LMetrics_Policy_Specs.

(* ---------------------------------------------------------------------- *)
(* Lemma costruttivo di separazione                                      *)
(* ---------------------------------------------------------------------- *)

Lemma Loventre_Safe_vs_NP_like_black_hole_separated :
  forall (m : LMetrics),
    loventre_global_decision m = GD_safe ->
    ~(loventre_global_decision m = GD_unsafe).
Proof.
  intros m Hsafe Hcontra.
  rewrite Hsafe in Hcontra. discriminate.
Qed.

(* ---------------------------------------------------------------------- *)
(* Lemmi di coerenza semantica minimale                                   *)
(* ---------------------------------------------------------------------- *)

Lemma Loventre_Safe_implies_P_like :
  forall (m : LMetrics),
    loventre_global_decision m = GD_safe ->
    P_like m.
Proof.
  intros m Hs.
  apply policy_safe_implies_P_like.
  exact Hs.
Qed.

Lemma Loventre_Unsafe_implies_NP_like_black_hole :
  forall (m : LMetrics),
    loventre_global_decision m = GD_unsafe ->
    NP_like m.
Proof.
  intros m Hu.
  apply policy_unsafe_implies_NP_like_black_hole.
  exact Hu.
Qed.

