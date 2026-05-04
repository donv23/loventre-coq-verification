(******************************************************************************)
(*                                                                            *)
(*  Attractor_Trichotomy.v                                                    *)
(*                                                                            *)
(*  Structural trichotomy of attractors                                       *)
(*                                                                            *)
(*  No time, no limits, no convergence.                                       *)
(*  Pure structural classification.                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Logic.

Require Import Structural_Core.LMetrics_Base.
Require Import Structural_Core.Structural_Dynamics_Abstract.
Require Import Structural_Thresholds.Thresholds_Abstract.
Require Import Structural_Attractors.Attractors_Abstract.
Require Import Structural_Attractors.Attractor_Isolating.

(******************************************************************************)
(*  Structural boundary axioms                                                *)
(******************************************************************************)

(* Critical structures exclude isolating threshold: structural boundary. *)
Axiom Critical_not_Isolating :
  forall L : LMetrics,
    Below_Critical_Threshold L ->
    ~ Below_Isolating_Threshold L.

(******************************************************************************)
(*  No attractor can live entirely in the critical region                      *)
(******************************************************************************)

Axiom No_critical_attractor :
  forall A : LMetrics -> Prop,
    Attractor A ->
    (forall L : LMetrics, A L -> Below_Critical_Threshold L) ->
    False.

Theorem No_pure_critical_attractor :
  forall A : LMetrics -> Prop,
    Attractor A ->
    (forall L : LMetrics, A L -> Below_Critical_Threshold L) ->
    False.
Proof.
  intros A Hattr Hall.
  exact (No_critical_attractor A Hattr Hall).
Qed.

(******************************************************************************)
(*  Structural attractor trichotomy (axiomatic frontier)                       *)
(******************************************************************************)

Axiom Structural_Attractor_Trichotomy :
  forall A : LMetrics -> Prop,
    Attractor A ->
    (A = Isolating_Region)
    \/ (forall L : LMetrics, A L -> Above_Stable_Threshold L)
    \/ False.

(******************************************************************************)
(*  End of file                                                               *)
(******************************************************************************)

