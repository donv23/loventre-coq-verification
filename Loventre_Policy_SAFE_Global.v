From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_SAFE_Predicate.
Require Import Loventre_Policy_Bridge.

(* =================================================== *)
(*  Canvas 38 — SAFE → POLICY → GLOBAL DECISION         *)
(* =================================================== *)

Theorem Loventre_Policy_from_SAFE :
  Loventre_Global_Decision P_STR.
Proof.
  constructor.
Qed.

(* =================================================== *)
(*  Fine Canvas 38                                      *)
(* =================================================== *)

