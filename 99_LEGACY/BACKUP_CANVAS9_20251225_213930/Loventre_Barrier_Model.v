(** Loventre_Barrier_Model.v
    Modello di barriera e dinamica oltre barriera nel modello Loventre. *)

From Coq Require Import Arith ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params.

From Loventre_Advanced Require Import
  Loventre_Potential_Field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

Open Scope Z_scope.

(** ============================================================= *)
(** Predicati di barriera su stati singoli                         *)
(** ============================================================= *)

Definition under_barrier (x : State) : Prop :=
  (U_L x < V0_L)%Z.

Definition over_barrier (x : State) : Prop :=
  (U_L x >= V0_L)%Z.

Definition barrier_region (x : State) : Prop :=
  over_barrier x.

(** ============================================================= *)
(** Dinamica lungo il flusso                                      *)
(** ============================================================= *)

Definition beyond_barrier_from (x : State) (n0 : nat) : Prop :=
  forall n : nat,
    (n >= n0)%nat ->
    over_barrier (Flow n x).

Definition barrier_segment (x : State) (n : nat) : Prop :=
  forall k : nat,
    (k <= a_min_L)%nat ->
    under_barrier (Flow (n + k)%nat x).

