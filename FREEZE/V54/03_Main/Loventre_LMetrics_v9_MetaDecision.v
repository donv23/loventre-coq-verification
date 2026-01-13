(** 
  Loventre_LMetrics_v9_MetaDecision.v
  Strato MetaDecision v9
 *)

From Stdlib Require Import Reals Bool.Bool.
From Loventre_Advanced Require Import Loventre_Metrics_Bus.
From Loventre_Main Require Import Loventre_GlobalDecision_Core.
From Loventre_Main Require Import Loventre_GlobalDecision_View.
From Loventre_Main Require Import Loventre_LMetrics_v9_SAFE.
From Loventre_Main Require Import Loventre_LMetrics_v9_Aliases.
From Loventre_Main Require Import Loventre_LMetrics_v9_Policy.
From Loventre_Main Require Import Loventre_Main_Theorem_v9_Prelude.

Import Loventre_Metrics_Bus.

Open Scope R_scope.

(** Per ora MetaDecision è un wrapper identitario sul livello Policy *)
Definition apply_meta_decision_to_metrics (m : LMetrics_v9) : LMetrics_v9 :=
  apply_policy_to_metrics m.

