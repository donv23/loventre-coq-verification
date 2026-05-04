(*
  LAB-12.1 — Core_Minimal.v

  Minimal structural core:
  - configurations
  - transitions
  - ONE single axiom

  No trichotomy.
  No terminality.
  No global rigidity.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Primitive objects === *)

Parameter Config : Type.
Parameter trans : Config -> Config -> Prop.

(* === Optional structural predicates === *)

Parameter Stable : Config -> Prop.
Parameter Critical : Config -> Prop.
Parameter Isolating : Config -> Prop.

(* === SINGLE axiom: local irreversibility === *)

Axiom local_irreversibility :
  forall x y : Config,
    trans x y ->
    Isolating y ->
    ~ trans y x.

