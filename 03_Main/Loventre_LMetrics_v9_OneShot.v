(** 
  Loventre_LMetrics_v9_OneShot.v
  Strato OneShot: SAFE → Policy → MetaDecision
 *)

From Stdlib Require Import Reals Bool.Bool.
From Loventre_Advanced Require Import Loventre_Metrics_Bus.
From Loventre_Main Require Import Loventre_GlobalDecision_Core.
From Loventre_Main Require Import Loventre_GlobalDecision_View.
From Loventre_Main Require Import Loventre_LMetrics_v9_SAFE.
From Loventre_Main Require Import Loventre_LMetrics_v9_Aliases.
From Loventre_Main Require Import Loventre_LMetrics_v9_Policy.
From Loventre_Main Require Import Loventre_LMetrics_v9_MetaDecision.
From Loventre_Main Require Import Loventre_Main_Theorem_v9_Prelude.

Import Loventre_Metrics_Bus.

Open Scope R_scope.

Definition loventre_lmetrics_v9_oneshot (m : LMetrics_v9) : LMetrics_v9 :=
  let m1 := m in
  let m2 := apply_policy_to_metrics m1 in
  let m3 := apply_meta_decision_to_metrics m2 in
  m3.

