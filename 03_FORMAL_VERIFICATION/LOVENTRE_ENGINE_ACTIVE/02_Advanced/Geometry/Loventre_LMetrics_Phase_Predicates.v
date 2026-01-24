(** Loventre_LMetrics_Phase_Predicates.v
    Predicati di fase (semantica parziale, non dicotomica)
    LIVELLO: Geometry (canonico)
*)

From Stdlib Require Import Reals.Rdefinitions Reals.Raxioms.

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_LMetrics_Structure.

Import Loventre_Metrics_Bus.

Module Loventre_LMetrics_Phase_Predicates.

  (** Una metrica ha “orizzonte” se horizon_flag = true *)
  Definition has_horizon (m : LMetrics) : Prop :=
    m.(horizon_flag) = true.

  (** Compattezza positiva: chi_compactness > 0 *)
  Definition compact_positive (m : LMetrics) : Prop :=
    (0 < m.(chi_compactness))%R.

  (** Stato NP-like (non esaustivo) *)
  Definition is_NP_like (m : LMetrics) : Prop :=
    compact_positive m /\ has_horizon m.

  (** Stato P-like (non esaustivo) *)
  Definition is_P_like (m : LMetrics) : Prop :=
    (~ compact_positive m) /\ (m.(horizon_flag) = false).

End Loventre_LMetrics_Phase_Predicates.

