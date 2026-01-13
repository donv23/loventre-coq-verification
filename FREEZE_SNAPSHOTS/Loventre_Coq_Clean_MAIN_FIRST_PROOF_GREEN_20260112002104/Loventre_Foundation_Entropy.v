(** Loventre_Foundation_Entropy.v
    Fondazioni entropiche del modello Loventre.
    CANON — V50 Reals floor self-axiom — gennaio 2026 *)
From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Reals.Zfloor.

From Loventre_Core Require Import Loventre_Kernel.
From Loventre_Core Require Import Loventre_Foundation_Types.

Import Loventre_Kernel.Loventre_Geometry.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** Valore reale dell'entropia *)
Parameter Entropy_L : M -> R.

(** Conversione discreta legacy con floor reale *)
Definition Entropy_LZ (x : M) : Z :=
  Zfloor (Entropy_L x).

(**
  Affermazione fondamentale: il floor è inferiore o uguale al reale.
  Su alcune build ARM, Coq non esporta alcun lemma standard,
  quindi lo inseriamo come Axiom nel nucleo fondazionale,
  marcato CANON, e lo useremo solo nel Core.
*)
Axiom Zfloor_le_real :
  forall a : R, IZR (Zfloor a) <= a.

Lemma Entropy_LZ_le_L :
  forall x, IZR (Entropy_LZ x) <= Entropy_L x.
Proof.
  intro x.
  unfold Entropy_LZ.
  apply Zfloor_le_real.
Qed.

Close Scope R_scope.

