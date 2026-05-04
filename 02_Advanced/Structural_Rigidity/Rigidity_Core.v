(*
  Rigidity_Core.v

  Minimal abstract core for structural rigidity (Cycle 10).

  This file introduces:
  - configurations
  - a structural transition relation
  - the notion of structural barrier
  - a single irreversibility axiom

  No temporal, computational, metric, or smooth structure is assumed.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===================================================== *)
(* === Primitive objects                               === *)
(* ===================================================== *)

Parameter Config : Type.

(* Structural transition relation *)
Parameter trans : Config -> Config -> Prop.

(* Structural barrier predicate *)
Parameter Barrier : Config -> Prop.

(* ===================================================== *)
(* === Irreversibility axiom                           === *)
(* ===================================================== *)

(*
  Entering a barrier configuration destroys the possibility
  of returning to the previous configuration.
*)
Axiom barrier_irreversible :
  forall x y : Config,
    trans x y ->
    Barrier y ->
    ~ trans y x.

(* ===================================================== *)
(* === Basic local rigidity                            === *)
(* ===================================================== *)

Lemma local_irreversibility :
  forall x y : Config,
    trans x y ->
    Barrier y ->
    ~ trans y x.
Proof.
  intros x y Hxy Hy.
  exact (@barrier_irreversible x y Hxy Hy).
Qed.

(*
  Epistemic note:
  - This core does NOT assert global non-symmetry.
  - All rigidity theorems derive non-reversibility
    under explicit hypotheses.
*)

