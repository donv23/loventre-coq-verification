(*
  CounterModel_EdgeNotPath.v
  LAB-11.2

  Edge irreversibility and path irreversibility are logically independent:
  this countermodel violates both.
*)

Require Import
  Loventre_Advanced.LAB_11_Axiom_Breaking.L11_2_IrrevHierarchy.IrrevHierarchy_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Abstract configurations === *)

Parameter a b c : Config.

(* === Transitions === *)

Axiom Hab : trans a b.
Axiom Hbc : trans b c.
Axiom Hcb : trans c b.

Axiom no_other :
  forall x y : Config,
    trans x y ->
    (x = a /\ y = b) \/
    (x = b /\ y = c) \/
    (x = c /\ y = b).

(* === Edge irreversibility fails === *)

Lemma c_not_IrrevEdge : ~ IrrevEdge c.
Proof.
  unfold IrrevEdge.
  intro H.
  apply (H b).
  - exact Hbc.
  - exact Hcb.
Qed.

(* === Path irreversibility also fails === *)

Lemma c_not_IrrevPath : ~ IrrevPath c.
Proof.
  unfold IrrevPath.
  intro H.
  apply (H b).
  - exact Hbc.
  - apply reach_step with (y := b).
    + exact Hcb.
    + apply reach_refl.
Qed.

