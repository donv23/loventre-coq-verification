From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_v3_LClass.

(* =================================================== *)
(* Loventre v3 — Policy semantica                      *)
(* =================================================== *)

Inductive LPolicy_v3 : Type :=
  | L_GREEN
  | L_AMBER
  | L_RED.

(* =================================================== *)
(* Mapping v3: Classi → Policy                         *)
(* =================================================== *)

Definition Loventre_v3_Policy_map (c : LClass_v3) : LPolicy_v3 :=
  match c with
  | P_STR => L_GREEN
  | P_ACC => L_AMBER
  | P_BH  => L_RED
  end.

