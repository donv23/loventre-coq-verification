From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_v3_LClass.

(* =================================================== *)
(* Loventre v3 — Informational Curvature               *)
(* =================================================== *)

(* κ : misura di curvatura informazionale             *)
(* (0 → stabile, 1 → accessibile critica, 2 → BH)     *)

Definition Loventre_v3_kappa (c : LClass_v3) : nat :=
  match c with
  | P_STR => 0
  | P_ACC => 1
  | P_BH  => 2
  end.

