From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_SAFE_Predicate.
Require Import Loventre_Policy_Bridge.
Require Import Loventre_Policy_SAFE_Global.

(* =================================================== *)
(* Canvas 39 — Policy Global Export                    *)
(* =================================================== *)

(*  Esportiamo la decisione globale GREEN              *)

Theorem Loventre_Witness_POLICY_GLOBAL :
  Loventre_Global_Decision P_STR.
Proof.
  apply Loventre_Policy_from_SAFE.
Qed.

(* =================================================== *)
(* Fine Canvas 39                                      *)
(* =================================================== *)

