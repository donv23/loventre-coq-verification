From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_v3_LClass.
Require Import Loventre_v3_Curvature.
Require Import Coq.micromega.Lia.

(* =================================================== *)
(* Loventre v3 — Separazione strutturale tramite κ      *)
(* =================================================== *)

Lemma Loventre_v3_kappa_STR_ACC :
  Loventre_v3_kappa P_STR < Loventre_v3_kappa P_ACC.
Proof.
  simpl. lia.
Qed.

Lemma Loventre_v3_kappa_ACC_BH :
  Loventre_v3_kappa P_ACC < Loventre_v3_kappa P_BH.
Proof.
  simpl. lia.
Qed.

