From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_v3_LClass.
Require Import Loventre_v3_Curvature.

(* =================================================== *)
(* Loventre v3 — Delta Curvatura Informazionale        *)
(* =================================================== *)

(* Nota:
   κ(P_STR)=0, κ(P_ACC)=1, κ(P_BH)=2.
   Dunque κ(c2) - κ(c1) è sempre >= 0.
   Questo rende la definizione di delta curvatura
   semplice e intrinsecamente monotona.            *)

Definition Loventre_v3_delta_kappa (c1 c2 : LClass_v3) : nat :=
  Loventre_v3_kappa c2 - Loventre_v3_kappa c1.

