(*
  LAB-12.3 — Triplet minimal rigidity core
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Abstract configurations === *)

Parameter Config : Type.
Parameter trans : Config -> Config -> Prop.

(* === Three regimes === *)

Parameter R1 R2 R3 : Config -> Prop.

Axiom R1R2_excl : forall x, ~(R1 x /\ R2 x).
Axiom R2R3_excl : forall x, ~(R2 x /\ R3 x).
Axiom R1R3_excl : forall x, ~(R1 x /\ R3 x).

(* === No global regime coverage === *)

Definition TripletCover :=
  forall x, R1 x \/ R2 x \/ R3 x.

