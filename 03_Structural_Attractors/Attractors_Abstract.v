(******************************************************************************)
(*                                                                            *)
(*  Attractors_Abstract.v                                                     *)
(*                                                                            *)
(*  Abstract structural attractors over LMetrics                              *)
(*                                                                            *)
(*  No time, no limits, no convergence.                                       *)
(*  Only irreversible structural confinement.                                 *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Logic.

Require Import Structural_Core.LMetrics_Base.
Require Import Structural_Core.Structural_Dynamics_Abstract.
Require Import Structural_Thresholds.Thresholds_Abstract.

(******************************************************************************)
(*  Abstract notion of structural attractor                                   *)
(******************************************************************************)

Parameter Attractor : (LMetrics -> Prop) -> Prop.

(******************************************************************************)
(*  Structural axioms for attractors                                          *)
(******************************************************************************)

(* Invariance under flow *)
Axiom Attractor_invariant :
  forall A : LMetrics -> Prop,
    Attractor A ->
    forall L1 L2 : LMetrics,
      A L1 ->
      L1 ~~> L2 ->
      A L2.

(* Local absorption *)
Axiom Attractor_absorbing :
  forall A : LMetrics -> Prop,
    Attractor A ->
    forall L : LMetrics,
      (exists L', L ~~> L' /\ A L') ->
      A L.

(******************************************************************************)
(*  End of file                                                               *)
(******************************************************************************)

