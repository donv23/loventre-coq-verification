(** 
  Loventre_LMetrics_v9_Risk.v
  Strato Risk classificato su LMetrics_v9
 *)

From Stdlib Require Import Reals Bool.Bool.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

From Loventre_Main Require Import Loventre_LMetrics_v9_Aliases.

Set Implicit Arguments.
Unset Strict Implicit.

(** Classificazioni elementari di rischio *)
Definition is_low (m : LMetrics_v9) : Prop :=
  risk_class m = risk_low.

Definition is_medium (m : LMetrics_v9) : Prop :=
  risk_class m = risk_medium.

Definition is_critical (m : LMetrics_v9) : Prop :=
  risk_class m = risk_np_like_critico.

Definition is_blackhole (m : LMetrics_v9) : Prop :=
  risk_class m = risk_np_like_black_hole.

(** Condizioni near-horizon = bool della metrica *)
Definition is_near_horizon_risk (m : LMetrics_v9) : Prop :=
  horizon_flag m = true.

(** Bucket di rischio v9 — classificazione bozza *)
Definition risk_bucket_v9 (m : LMetrics_v9) : Prop :=
     is_low m
  \/ is_medium m
  \/ is_critical m
  \/ is_blackhole m.

Lemma risk_bucket_sound :
  forall m : LMetrics_v9, risk_bucket_v9 m -> True.
Proof.
  intros m _. exact I.
Qed.

