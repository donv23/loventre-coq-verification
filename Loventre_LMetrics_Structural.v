(** ============================================================= *)
(**   Loventre_LMetrics_Structural.v — Canvas 17                 *)
(** ============================================================= *)

From Stdlib Require Import Arith.

Require Import Loventre_LMetrics_Kernel.
Require Import Loventre_Meta_Theorem.

Section LMetrics_Structural.

  Variable Witness : Type.

  Variable is_P_like   : Witness -> Prop.
  Variable is_NP_like  : Witness -> Prop.

  Variable reducible   : Witness -> Witness -> Prop.
  Variable equivalent  : Witness -> Witness -> Prop.

  Variable PWitness : nat -> Witness.
  Variable NPWitness : nat -> Witness.

  Hypothesis H_P_like_family :
    forall (n : nat), is_P_like (PWitness n).

  Hypothesis H_NP_like_family :
    forall (n : nat), is_NP_like (NPWitness n).

  Hypothesis H_irreducible :
    forall (Wp : Witness) (Wnp : Witness),
      is_P_like Wp ->
      is_NP_like Wnp ->
      ~ reducible Wnp Wp.

  Hypothesis H_equiv_implies_reducible :
    forall (Wp : Witness) (Wnp : Witness),
      equivalent Wnp Wp ->
      reducible Wnp Wp.

  Variable LProfile_of : Witness -> LMetrics.

  Theorem LMetrics_inherit_separation :
    (forall w, LM_legal (LProfile_of w)) ->
    ~ P_like_equiv_NP_like Witness is_P_like is_NP_like equivalent.
  Proof.
    intro Hlegal.
    apply meta_separation
      with (PWitness := PWitness)
           (NPWitness := NPWitness)
           (reducible := reducible)
           (equivalent := equivalent);
      assumption.
  Qed.

End LMetrics_Structural.

