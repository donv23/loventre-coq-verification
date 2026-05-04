(** Loventre_Mass_Equivalence.v
    Massa informazionale e relazioni di monotonia. *)

From Coq Require Import ZArith Arith.

Require Import Loventre_Kernel.
Require Import Loventre_Foundation_Types.
Require Import Loventre_Foundation_Complexity.
Require Import Loventre_Curvature_Field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

Parameter mass_L : State -> Z.

Definition mass_equiv (x y : State) : Prop :=
  mass_L x = mass_L y.

(** Monotonia della massa rispetto alla curvatura informazionale. *)

Axiom mass_curvature_monotone :
  forall x y : State,
    (kappa_L x <= kappa_L y)%Z ->
    (mass_L x <= mass_L y)%Z.

(** Monotonia della massa rispetto alla complessità (in senso astratto). *)

Axiom mass_complexity_monotone :
  forall x y : State,
    Complexity_L x <= Complexity_L y ->
    (mass_L x <= mass_L y)%Z.

