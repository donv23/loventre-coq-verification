From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_SAFE_Predicate.
Require Import Loventre_v3_LClass.
Require Import Loventre_v3_DeltaCurvature.
Require Import Loventre_Witness_SAFE_Global.

(* =================================================== *)
(* LOVENTRE v6 — Curvature SAFE Barrier                *)
(* =================================================== *)

(* Monotonicità di Curvatura: BH è attrattore *)
Lemma Loventre_v6_curvature_monotone :
  Loventre_v3_delta_kappa P_BH P_BH >=
  Loventre_v3_delta_kappa Witness_LClass P_BH.
Proof.
  simpl.
  lia.
Qed.

(* SAFE Barrier: SAFE non può diventare non-SAFE *)
Lemma Loventre_v6_SAFE_barrier :
  Loventre_SAFE Witness_LClass ->
  Loventre_SAFE P_BH.
Proof.
  intro H.
  (* costruzione minimale: BH rispetta SAFE *)
  (* perché non vi è riduzione di curvatura spettrale *)
  apply Safe_PSTR.
Qed.

(* Teorema finale v6 *)
Theorem Loventre_v6_SAFE_BH_Barrier :
  Loventre_SAFE Witness_LClass /\ Loventre_SAFE P_BH.
Proof.
  split.
  - apply Witness_is_SAFE.
  - apply Loventre_v6_SAFE_barrier.
    apply Witness_is_SAFE.
Qed.

