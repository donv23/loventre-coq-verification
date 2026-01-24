(** Loventre_Potential_Field.v
    Campo di potenziale informazionale nel modello Loventre.
    CANON — dicembre 2025 *)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Entropy
  Loventre_Foundation_Params.

From Loventre_Advanced Require Import
  Loventre_Curvature_Field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z_scope.

(* Import del modulo geometrico dal Kernel *)
Import Loventre_Kernel.Loventre_Geometry.

(** Potenziale Loventre:
    U_L(x) = alpha_L * kappa_L(x) + beta_L * Entropy_L(x) *)

Definition U_L (x : M) : Z :=
  alpha_L * kappa_L x + beta_L * Entropy_L x.

Lemma U_L_linear_in_kappa_entropy :
  forall x : M,
    U_L x = alpha_L * kappa_L x + beta_L * Entropy_L x.
Proof.
  intro x; reflexivity.
Qed.

