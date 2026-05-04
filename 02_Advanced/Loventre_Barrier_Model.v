(** Loventre_Barrier_Model.v
    Modello di barriera e dinamica oltre barriera nel modello Loventre.
    LIVELLO: Advanced — CANON
*)

From Stdlib Require Import Arith ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params.

From Loventre_Advanced Require Import
  Loventre_Potential_Field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z_scope.

Import Loventre_Geometry.

(** ================================================================ *)
(** Parametro di barriera (astratto, livello Advanced)               *)
(** ================================================================ *)

Parameter V0_L : Z.

(** ================================================================ *)
(** Predicati di barriera su stati                                   *)
(** ================================================================ *)

Definition under_barrier (x : M) : Prop :=
  (U_L x < V0_L)%Z.

Definition over_barrier (x : M) : Prop :=
  (U_L x >= V0_L)%Z.

Definition barrier_region (x : M) : Prop :=
  over_barrier x.

(** ================================================================ *)
(** Dinamica lungo il flusso                                         *)
(** ================================================================ *)

Definition beyond_barrier_from (x : M) (n0 : nat) : Prop :=
  forall n : nat,
    (n >= n0)%nat ->
    over_barrier (Flow n x).

Definition barrier_segment (x : M) (n : nat) : Prop :=
  forall k : nat,
    (k <= a_min_L)%nat ->
    under_barrier (Flow (n + k)%nat x).

