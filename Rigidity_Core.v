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
(* === Basic rigidity consequence                      === *)
(* ===================================================== *)

Lemma no_global_symmetry :
  (exists b : Config, Barrier b) ->
  ~ (forall x y : Config, trans x y -> trans y x).
Proof.
  intros [b Hb] Hsym.
  specialize (Hsym b b).
  assert (trans b b -> False).
  {
    intro H.
    apply (barrier_irreversible b b H Hb).
  }
  apply H0.
  apply Hsym.
Qed.

(*
  Epistemic note:
  - All rigidity theorems in Cycle 10 depend ONLY on this file.
  - barrier_irreversible is the only nontrivial axiom.
*)

