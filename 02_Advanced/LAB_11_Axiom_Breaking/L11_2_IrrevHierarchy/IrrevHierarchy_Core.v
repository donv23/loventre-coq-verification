(*
  IrrevHierarchy_Core.v
  LAB-11.2 (reformulated):
  Edge-irreversibility vs Path-irreversibility.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Primitive structure *)
Parameter Config : Type.
Parameter trans : Config -> Config -> Prop.

(* Reachability *)
Inductive reach : Config -> Config -> Prop :=
| reach_refl : forall x, reach x x
| reach_step : forall x y z,
    trans x y ->
    reach y z ->
    reach x z.

(* Irreversibility notions *)

Definition IrrevEdge (y : Config) : Prop :=
  forall x : Config, trans x y -> ~ trans y x.

Definition IrrevPath (y : Config) : Prop :=
  forall x : Config, trans x y -> ~ reach y x.

(* Path-irreversibility is strictly stronger *)

Lemma IrrevPath_implies_IrrevEdge :
  forall y : Config,
    IrrevPath y -> IrrevEdge y.
Proof.
  intros y Hpath x Hxy Hyx.
  apply (Hpath x Hxy).
  apply (@reach_step y x x).
  - exact Hyx.
  - apply (@reach_refl x).
Qed.

