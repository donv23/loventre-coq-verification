(** Loventre_LMetrics_v9_Aliases.v
    Alias di comodo per LMetrics v9, coerente con Loventre_Metrics_Bus
 *)

From Stdlib Require Import Reals Bool.Bool.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Unset Strict Implicit.

(* Alias di comodo al tipo ufficiale *)
Definition LMetrics_v9 := LMetrics.

(* Alias semplici ai predicati definiti nel bus *)
Definition is_low_risk (m : LMetrics_v9) : Prop :=
  is_subcritical m.

Definition is_medium_risk (m : LMetrics_v9) : Prop :=
  is_precritical_or_mixed m.

Definition is_crit_risk (m : LMetrics_v9) : Prop :=
  is_np_like_critical m.

Definition is_bh_risk (m : LMetrics_v9) : Prop :=
  is_black_hole_like m.

(* Alias alle decisioni globali *)
Definition is_safe_global (m : LMetrics_v9) : Prop :=
  is_globally_safe m.

Definition is_critical_global (m : LMetrics_v9) : Prop :=
  is_globally_critical m.

Definition is_invalid_global (m : LMetrics_v9) : Prop :=
  is_globally_invalid m.

