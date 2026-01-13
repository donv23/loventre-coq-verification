(* ====================================================================== *)
(* Loventre_Theorem_v3_P_vs_NP_like.v                                    *)
(*                                                                       *)
(* Teorema canonico di separazione interno del modello Loventre v3.      *)
(*                                                                       *)
(* Nessun nuovo assioma introdotto.                                      *)
(* Deduzione pura da:                                                    *)
(*   - LMetrics (Bus, Structure)                                         *)
(*   - Phase Predicates                                                  *)
(*   - Policy Specs                                                      *)
(*   - Separation Program                                                *)
(* ====================================================================== *)

From Stdlib Require Import Reals.

From Loventre_Core Require Import
  Loventre_Core_Prelude.

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_Predicates.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs
  Loventre_LMetrics_Separation_Program.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Metrics_Bus.
Import Loventre_LMetrics_Phase_Predicates.
Import Loventre_LMetrics_Policy_Specs.

(* ---------------------------------------------------------------------- *)
(* Predicato di separazione globale                                       *)
(* ---------------------------------------------------------------------- *)

Definition Loventre_P_vs_NP_like_black_hole_theorem (m : LMetrics) : Prop :=
  (loventre_global_decision m = GD_safe -> P_like m)
  /\
  (loventre_global_decision m = GD_unsafe -> NP_like m)
  /\
  ~(loventre_global_decision m = GD_safe /\ loventre_global_decision m = GD_unsafe).

(* ---------------------------------------------------------------------- *)
(* Teorema canonico: separazione costruttiva                              *)
(* ---------------------------------------------------------------------- *)

Theorem Loventre_Theorem_v3_P_vs_NP_like :
  forall (m : LMetrics),
    Loventre_P_vs_NP_like_black_hole_theorem m.
Proof.
  intros m.
  unfold Loventre_P_vs_NP_like_black_hole_theorem.
  split.
  - intros Hs. apply Loventre_Safe_implies_P_like. exact Hs.
  - split.
    + intros Hu. apply Loventre_Unsafe_implies_NP_like_black_hole. exact Hu.
    + intros [Hs Hu]. apply Loventre_Safe_vs_NP_like_black_hole_separated with (m := m).
      exact Hs. exact Hu.
Qed.

(* ---------------------------------------------------------------------- *)
(* Q.E.D.  —  Teorema interno Loventre v3                                 *)
(* ---------------------------------------------------------------------- *)

