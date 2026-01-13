(** Loventre_Regimes_Properties.v
    Proprietà sui riepiloghi di regime.
    CANON — V50 (entropia reale + proiezione Zfloor corretta) *)

From Stdlib Require Import Reals ZArith Zfloor.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Entropy
  Loventre_Foundation_Params
  Loventre_Zfloor_Lemmas.

From Loventre_Advanced Require Import
  Loventre_Regimes_Definition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Kernel.Loventre_Geometry.

Open Scope R_scope.

(** ======================================================= *)
(** Derivata intera dell’entropia tramite Zfloor             *)
(** ======================================================= *)

Definition regime_entropy_Z (rs : loventre_regime_summary) : Z :=
  Zfloor (regime_entropy rs).

Lemma regime_entropy_Z_le_real :
  forall rs, (IZR (regime_entropy_Z rs) <= regime_entropy rs)%R.
Proof.
  intro rs.
  unfold regime_entropy_Z.
  apply Loventre_Zfloor_lb.
Qed.

Lemma regime_entropy_Z_bounds :
  forall rs,
    (IZR (regime_entropy_Z rs) <= regime_entropy rs <
     IZR (regime_entropy_Z rs) + 1)%R.
Proof.
  intro rs.
  unfold regime_entropy_Z.
  apply Loventre_Zfloor_bounds.
Qed.

(** ======================================================= *)
(** Monotonia floor (Z) coerente al modello                 *)
(** ======================================================= *)

Lemma regime_entropy_Z_le_trans :
  forall rs1 rs2,
    (regime_entropy rs1 <= regime_entropy rs2)%R ->
    (regime_entropy_Z rs1 <= regime_entropy_Z rs2)%Z.
Proof.
  intros rs1 rs2 Hle.
  unfold regime_entropy_Z.
  apply Loventre_Zfloor_monotone; exact Hle.
Qed.

Close Scope R_scope.

