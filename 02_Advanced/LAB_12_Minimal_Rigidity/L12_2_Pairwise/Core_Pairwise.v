(*
  LAB-12.2 — Core_Pairwise.v

  Two axioms are assumed together:
  - local irreversibility
  - terminal isolation

  We investigate whether they force global rigidity.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Abstract configurations === *)

Parameter Config : Type.

(* === Transition relation === *)

Parameter trans : Config -> Config -> Prop.

(* === Assumptions === *)

(* Local irreversibility: no immediate 2-cycles *)
Axiom IrrevLocal :
  forall x y : Config,
    trans x y -> ~ trans y x.

(* Terminal isolation *)
Parameter Isolating : Config -> Prop.
Axiom terminal_isolated :
  forall x y : Config,
    Isolating x -> ~ trans x y.

(* === Global rigidity (target property) === *)

Definition GlobalRigid : Prop :=
  forall x y : Config,
    trans x y -> ~ trans y x.

