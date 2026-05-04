(******************************************************************************)
(*                                                                            *)
(*  Attractor_Isolating.v                                                     *)
(*                                                                            *)
(*  Isolating region as a primitive structural attractor                      *)
(*                                                                            *)
(*  All properties in this file are structural axioms, not derived results.   *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Logic.

Require Import Structural_Core.LMetrics_Base.
Require Import Structural_Core.Structural_Dynamics_Abstract.
Require Import Structural_Thresholds.Thresholds_Abstract.
Require Import Structural_Attractors.Attractors_Abstract.

(******************************************************************************)
(*  Isolating region                                                          *)
(******************************************************************************)

Definition Isolating_Region (L : LMetrics) : Prop :=
  Below_Isolating_Threshold L.

(******************************************************************************)
(*  Primitive structural axioms                                               *)
(******************************************************************************)

(* Closure of isolating region under flow *)
Axiom Isolating_closed_under_flow :
  forall L1 L2 : LMetrics,
    Isolating_Region L1 ->
    L1 ~~> L2 ->
    Isolating_Region L2.

(* Retro-absorption of isolating region *)
Axiom Isolating_retro_absorbing :
  forall L : LMetrics,
    (exists L', L ~~> L' /\ Isolating_Region L') ->
    Isolating_Region L.

(* Isolating region is a structural attractor *)
Axiom Isolating_is_attractor :
  Attractor Isolating_Region.

(******************************************************************************)
(*  End of file                                                               *)
(******************************************************************************)

