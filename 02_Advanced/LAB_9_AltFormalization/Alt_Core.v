(*
  Alt_Core.v
  LAB-9: Alternative core with intrinsic irreversibility.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Parameter Config : Type.
Parameter trans : Config -> Config -> Prop.

(* Intrinsic irreversibility predicate *)
Parameter irreversible : Config -> Prop.

(* Irreversibility axiom: points marked irreversible cannot be left backwards *)
Axiom intrinsic_irreversibility :
  forall x y : Config,
    trans x y ->
    irreversible y ->
    ~ trans y x.

