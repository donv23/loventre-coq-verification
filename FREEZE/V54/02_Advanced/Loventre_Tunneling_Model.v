(** Loventre_Tunneling_Model.v
    Modello di tunneling informazionale nel modello Loventre.
    CANON — dicembre 2025 *)

From Stdlib Require Import Arith ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Params.

From Loventre_Advanced Require Import
  Loventre_Barrier_Model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

Open Scope Z_scope.

(** ============================================================= *)
(** Alias canonico di stato                                       *)
(** ============================================================= *)

Definition State := Loventre_Geometry.M.

(** ============================================================= *)
(** Tunneling attraverso una barriera                             *)
(** ============================================================= *)

Definition can_tunnel (x : State) (n_start n_end : nat) : Prop :=
  (n_start + a_min_L <= n_end)%nat /\
  exists n : nat,
    (n_start <= n <= n_end)%nat /\
    under_barrier (Flow n x).

Definition eventual_tunneling (x : State) : Prop :=
  exists n_start n_end : nat,
    can_tunnel x n_start n_end.

