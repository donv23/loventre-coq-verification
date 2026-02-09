(*
  PNE_NP_Sanity.v

  Sanity check for the global principle PNE-NP
  No claims, no proofs, no consequences.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* =============================== *)
(* Basic notion of a language      *)
(* =============================== *)

Record Language := {
  inst : nat -> Type;
  valid : forall n : nat, inst n -> Prop
}.

(* =============================== *)
(* Abstract complexity predicates  *)
(* =============================== *)

Parameter NP_Hard : Language -> Prop.

(* =============================== *)
(* Structural global properties    *)
(* =============================== *)

Parameter GlobalConstraint : Language -> Prop.
Parameter NoLocalCertificates : Language -> Prop.
Parameter NonFoliable : Language -> Prop.

Definition NEC_star (L : Language) : Prop :=
  GlobalConstraint L /\
  NoLocalCertificates L /\
  NonFoliable L.

(* =============================== *)
(* Subfamilies                     *)
(* =============================== *)

Parameter Subfamily : Language -> Language -> Prop.

(* =============================== *)
(* Global candidate principle      *)
(* =============================== *)

Axiom PNE_NP :
  forall L : Language,
    NP_Hard L ->
    exists F : Language,
      Subfamily F L /\ NEC_star F.

(* =============================== *)
(* End of sanity file              *)
(* =============================== *)

