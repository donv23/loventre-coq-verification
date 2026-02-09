From Stdlib Require Import String.
Open Scope string_scope.

(* =================================================== *)
(* Loventre v3 — Definizione delle Classi              *)
(* =================================================== *)

Inductive LClass_v3 : Type :=
  | P_STR      (* baseline *)
  | P_ACC      (* accessibile *)
  | P_BH.      (* black-hole *)

