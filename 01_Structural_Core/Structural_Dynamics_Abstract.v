(******************************************************************************)
(*                                                                            *)
(*  Structural_Dynamics_Abstract.v                                            *)
(*                                                                            *)
(*  Abstract structural dynamics over LMetrics                                *)
(*                                                                            *)
(*  No time, no numerics, no energy.                                           *)
(*  Only irreversible structural relations.                                   *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Logic.

Require Import Structural_Core.LMetrics_Base.

(******************************************************************************)
(*  Abstract structural flow                                                   *)
(******************************************************************************)

(* Abstract reachability / evolution relation *)
Parameter FlowsTo : LMetrics -> LMetrics -> Prop.

Notation "L1 ~~> L2" := (FlowsTo L1 L2) (at level 60).

(******************************************************************************)
(*  Minimal structural axioms on the flow                                      *)
(******************************************************************************)

(* Reflexivity: every structure trivially flows to itself *)
Axiom Flow_refl :
  forall L : LMetrics, L ~~> L.

(* Transitivity: flows compose *)
Axiom Flow_trans :
  forall L1 L2 L3 : LMetrics,
    L1 ~~> L2 ->
    L2 ~~> L3 ->
    L1 ~~> L3.

(******************************************************************************)
(*  Structural irreversibility                                                 *)
(******************************************************************************)

(* No flow from isolating to stable *)
Axiom Isolating_irreversible :
  forall L1 L2 : LMetrics,
    Isolating L1 ->
    L1 ~~> L2 ->
    ~ Stable L2.

(******************************************************************************)
(*  First structural theorem                                                   *)
(******************************************************************************)

Theorem No_return_from_isolation :
  forall L1 L2 : LMetrics,
    Isolating L1 ->
    L1 ~~> L2 ->
    ~ Stable L2.
Proof.
  intros L1 L2 Hiso Hflow.
  apply Isolating_irreversible with (L1 := L1); assumption.
Qed.

(******************************************************************************)
(*  End of file                                                               *)
(******************************************************************************)

