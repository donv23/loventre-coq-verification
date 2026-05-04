(** Loventre_Barrier_Model.v
    Modello di barriera e dinamica oltre barriera nel modello Loventre. *)

From Stdlib Require Import Arith ZArith.

Require Import Loventre_Core.Loventre_Kernel.
Require Import Loventre_Core.Loventre_Foundation_Types.
Require Import Loventre_Core.Loventre_Foundation_Params.
Require Import Loventre_Advanced.Loventre_Potential_Field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

Open Scope Z_scope.

(* ================================================================ *)
(* Alias canonico: stato geometrico                                *)
(* ================================================================ *)

Definition State := Loventre_Geometry.M.

(* ================================================================ *)
(* Predicati di barriera                                           *)
(* ================================================================ *)

Definition under_barrier (x : State) : Prop :=
  (U_L x < V0_L)%Z.

Definition over_barrier (x : State) : Prop :=
  (U_L x >= V0_L)%Z.

Definition barrier_region (x : State) : Prop :=
  over_barrier x.

(* ================================================================ *)
(* Dinamica lungo il flusso                                        *)
(* ================================================================ *)

Definition beyond_barrier_from (x : State) (n0 : nat) : Prop :=
  forall n : nat,
    (n >= n0)%nat ->
    over_barrier (Flow n x).

Definition barrier_segment (x : State) (n : nat) : Prop :=
  forall k : nat,
    (k <= a_min_L)%nat ->
    under_barrier (Flow (n + k)%nat x).

