From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_SAFE_Predicate.

(* =================================================== *)
(*  Policy Bridge                                       *)
(* =================================================== *)

(*  SAFE ---> DECISION GLOBALE                         *)

Inductive Loventre_Global_Decision : LClass -> Prop :=
  | Policy_GREEN_from_SAFE : Loventre_Global_Decision P_STR.

