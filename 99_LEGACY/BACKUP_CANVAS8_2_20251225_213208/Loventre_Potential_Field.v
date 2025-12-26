(** Loventre_Potential_Field.v
    Campo di potenziale informazionale nel modello Loventre. *)

From Coq Require Import ZArith.

Require Import Loventre_Curvature_Field.
Require Import Loventre_Foundation_Entropy.
Require Import Loventre_Foundation_Params.
Require Import Loventre_Foundation_Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z_scope.

(** Potenziale Loventre:
      U_L(x) = alpha_L * kappa_L(x) + beta_L * Entropy_L(x) *)

Definition U_L (x : State) : Z :=
  alpha_L * kappa_L x + beta_L * Entropy_L x.

Lemma U_L_linear_in_kappa_entropy :
  forall x : State,
    U_L x = alpha_L * kappa_L x + beta_L * Entropy_L x.
Proof.
  intro x; reflexivity.
Qed.

