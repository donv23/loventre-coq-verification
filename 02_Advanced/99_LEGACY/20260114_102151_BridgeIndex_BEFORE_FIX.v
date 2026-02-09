(* ====================================================== *)
(* LOVENTRE ENGINE v7 — MINI BRIDGE INDEX                 *)
(* Raggruppa Core, Profile e Policy                       *)
(* ====================================================== *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
  LMetrics_v7_Prelude
  LMetrics_v7_types
  LMetrics_v7_import
  LMetrics_v7_CoreBridge
  LMetrics_v7_ProfileBridge
  LMetrics_v7_PolicyBridge.

(* Punto di aggregazione API *)
Record LMetricsV7_Bundle := {
  out_raw : LMetricsV7;
  out_profile : LMetricsV7_Profile;
  out_policy : Z
}.

Definition mk_bundle (w : LMetricsV7) : LMetricsV7_Bundle :=
  {| out_raw := w;
     out_profile := to_profile w;
     out_policy := policy_decide (to_profile w)
  |}.

Definition bundle_01 : LMetricsV7_Bundle :=
  mk_bundle witness_m_v7_3sat_DIMACS_01.

Lemma bundle_policy_is_valid :
  out_policy bundle_01 = 0%Z \/ out_policy bundle_01 = 1%Z.
Proof.
  unfold bundle_01, mk_bundle.
  destruct (policy_decision_is_defined); auto.
Qed.

