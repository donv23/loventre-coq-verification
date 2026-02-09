From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_Witness_Loader.
Require Import Loventre_SAFE_Predicate.
Require Import Loventre_SAFE_Bridge.
Require Import Loventre_Witness_SAFE_Global.

(* =================================================== *)
(* Canvas 37 — GLOBAL SAFE EXPORT                     *)
(* =================================================== *)

(*  Export finale e globale:                         *)
(*  Il Witness canonico (P_STR) è SAFE.              *)
(* =================================================== *)

Theorem Loventre_Witness_GLOBAL_SAFE :
  Loventre_SAFE P_STR.
Proof.
  apply Safe_PSTR.
Qed.

(* =================================================== *)
(*  Fine Canvas 37                                     *)
(* =================================================== *)

