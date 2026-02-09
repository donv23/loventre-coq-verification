From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_SAFE_Predicate.
Require Import Loventre_Policy_Bridge.
Require Import Loventre_Policy_Global_Export.
Require Import Loventre_Policy_JSON_Bridge.

(* =================================================== *)
(*  Canvas 41 — Loventre v2 — Chiusura formale         *)
(* =================================================== *)

(*  Dichiarazione finale:                              *)
(*  La Decisione Globale derivata dal Witness P_STR    *)
(*  è GREEN, ed è esportata stabilmente in JSON.       *)
(* =================================================== *)

Theorem Loventre_v2_Final :
  Loventre_Global_Decision P_STR /\ 
  Loventre_Policy_JSON_Global_Decision = "GREEN".
Proof.
  split.
  - apply Loventre_Witness_POLICY_GLOBAL.
  - reflexivity.
Qed.

(* =================================================== *)
(*  Fine Loventre v2                                   *)
(* =================================================== *)

