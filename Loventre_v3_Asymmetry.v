From Stdlib Require Import String.
From Stdlib Require Import Nat.
Open Scope string_scope.

Require Import Loventre_v3_LClass.
Require Import Loventre_v3_Curvature.
Require Import Loventre_v3_DeltaCurvature.

(* =================================================== *)
(* Loventre v3 — Asymmetry Lemma                      *)
(* =================================================== *)

Lemma Loventre_v3_asymmetry_final :
  S (Loventre_v3_delta_kappa P_ACC P_BH) <=
    Loventre_v3_delta_kappa P_STR P_BH.
Proof.
  simpl. auto.
Qed.

