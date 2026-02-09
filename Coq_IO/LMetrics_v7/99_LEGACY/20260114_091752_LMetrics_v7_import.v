(* LMetrics_v7_import.v — Canonico *)

From Stdlib Require Import ZArith.
From Stdlib Require Import String.
Require Import Coq.Strings.Ascii.

Open Scope Z_scope.
Open Scope string_scope.

Require Import Coq_IO.LMetrics_v7.LMetrics_v7_types.

(* Alias di convenienza per create *)
Definition mkv7
  (ke en me ii ri sclass dec col sc ml : Z)
  (src : string)
  : LMetrics_v7 :=
  mkLMetrics_v7 ke en me ii ri sclass dec col sc ml src.

(* Fine file *)

