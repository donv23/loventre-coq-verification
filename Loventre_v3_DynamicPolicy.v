From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_v3_LClass.
Require Import Loventre_v3_Curvature.
Require Import Loventre_v3_DeltaCurvature.
Require Import Loventre_v3_Policy.

(* =================================================== *)
(* Loventre v3 — Dynamic Policy                        *)
(* =================================================== *)

Definition Loventre_v3_dynamic_policy (c1 c2 : LClass_v3) : LPolicy_v3 :=
  match Loventre_v3_delta_kappa c1 c2 with
  | 0 => L_GREEN   (* No change in class *)
  | 1 => L_AMBER   (* Weak transition *)
  | _ => L_RED     (* Strong shift => black-hole *)
  end.

