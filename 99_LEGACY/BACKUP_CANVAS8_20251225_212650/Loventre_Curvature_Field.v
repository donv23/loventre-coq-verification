(** Loventre_Curvature_Field.v
    Campo di curvatura informazionale nel modello Loventre.
    CANON — dicembre 2025 *)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(** Alias coerenti con il motore Loventre. *)

Definition kappa_L (x : State) : Z :=
  kappa x.

Definition alpha_c_L : Z :=
  alpha_c.

Definition curvature_subcritical (x : State) : Prop :=
  subcritical x.

Definition curvature_supercritical (x : State) : Prop :=
  supercritical x.

Lemma curvature_subcritical_iff :
  forall x : State,
    curvature_subcritical x <-> (kappa_L x < alpha_c_L)%Z.
Proof.
  intro x.
  unfold curvature_subcritical, kappa_L, alpha_c_L, subcritical.
  tauto.
Qed.

Lemma curvature_supercritical_iff :
  forall x : State,
    curvature_supercritical x <-> (kappa_L x >= alpha_c_L)%Z.
Proof.
  intro x.
  unfold curvature_supercritical, kappa_L, alpha_c_L, supercritical.
  tauto.
Qed.

