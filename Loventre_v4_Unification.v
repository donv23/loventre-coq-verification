From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_Witness_SAFE_Global.
Require Import Loventre_SAFE_Predicate.

Require Import Loventre_v3_LClass.
Require Import Loventre_v3_DeltaCurvature.
Require Import Loventre_v3_Asymmetry.
Require Import Loventre_v3_Final.

(* =================================================== *)
(* LOVENTRE v4 — Unification Layer                     *)
(* =================================================== *)

(* SAFE (ereditato da witness concreto P_STR) *)
Definition Loventre_v4_system_is_SAFE : Prop :=
  Loventre_SAFE Witness_LClass.

(* Asimmetria informazionale verso BH *)
Definition Loventre_v4_asymmetry_valid : Prop :=
  S (Loventre_v3_delta_kappa P_ACC P_BH)
    <= Loventre_v3_delta_kappa P_STR P_BH.

(* Teorema di Unificazione v4 *)
Lemma Loventre_v4_unified :
  Loventre_v4_system_is_SAFE /\ Loventre_v4_asymmetry_valid.
Proof.
  split.
  - apply Witness_is_SAFE.
  - apply Loventre_v3_asymmetry_final.
Qed.

