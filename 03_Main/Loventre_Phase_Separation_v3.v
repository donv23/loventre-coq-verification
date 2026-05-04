(* ========================================================== *)
(*  LOVENTRE PROJECT — Loventre_Phase_Separation_v3.v         *)
(*  Dicembre 2025 — Separazione di fase P_acc vs NP_bh v3     *)
(*                                                            *)
(*  Obiettivo:                                                *)
(*    dimostrare, al livello LMetrics, che una configurazione *)
(*    NP_like-black-hole non può essere P_like_accessible.    *)
(*                                                            *)
(*    forall m, is_NP_like_black_hole m ->                    *)
(*               ~ is_P_like_accessible m.                    *)
(*                                                            *)
(*  Questo modulo lavora SOLO con:                            *)
(*    - il tipo astratto LMetrics (JSON_Witness);             *)
(*    - i predicati astratti is_NP_like_black_hole;           *)
(*    - i predicati di fase is_P_like_accessible,             *)
(*      is_black_hole, is_non_black_hole.                     *)
(* ========================================================== *)

From Coq Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates.

Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Module JSONW  := Loventre_LMetrics_JSON_Witness.
Module Ex     := Loventre_LMetrics_Existence_Summary.
Module Phase  := Loventre_LMetrics_Phase_Predicates.

Import JSONW Ex Phase.

(* ========================================================= *)
(*  Separazione di fase NP_like-black-hole vs P_acc          *)
(* ========================================================= *)

Lemma Loventre_NP_like_black_hole_not_P_like_accessible_v3 :
  forall m : LMetrics,
    is_NP_like_black_hole m ->
    ~ is_P_like_accessible m.
Proof.
  intros m Hnp Hacc.
  unfold is_P_like_accessible in Hacc.
  destruct Hacc as [HPlike _Hsafe].
  unfold is_P_like in HPlike.
  destruct HPlike as [_Hncomp HhorF].
  unfold is_NP_like_black_hole in Hnp.
  destruct Hnp as [HNPlike _Hrisk].
  unfold is_NP_like in HNPlike.
  destruct HNPlike as [_Hcomp HhorT].
  unfold has_horizon in HhorT.
  congruence.
Qed.

(* Goal di sanity locale. *)

Goal True. exact I. Qed.

