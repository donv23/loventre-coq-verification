From Coq Require Import Reals.
From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** Questo file raccoglie proprietà di Policy "ideali" come specifiche pure (Prop),
    senza assumere che siano vere. Il modulo di Policy potrà in futuro:
    - cercare di dimostrarle,
    - oppure adottarne versioni indebolite. *)

(** 1. Proprietà punto-per-punto (per un singolo LMetrics) *)

(** Nessuna configurazione black-hole deve risultare GC_green. *)
Definition policy_never_green_on_black_hole_pointwise (m : LMetrics) : Prop :=
  is_black_hole m -> loventre_global_color m <> GC_green.

(** Il colore GC_green è permesso solo su configurazioni low risk e non-black-hole. *)
Definition policy_green_only_on_low_risk_non_black_hole_pointwise (m : LMetrics) : Prop :=
  loventre_global_color m = GC_green ->
  is_low_risk m /\ is_non_black_hole m.

(** Una decisione GD_borderline colorata GC_green deve corrispondere
    a una configurazione P-like accessibile (borderline green). *)
Definition policy_borderline_green_matches_P_like_accessible_pointwise (m : LMetrics) : Prop :=
  loventre_global_decision m = GD_borderline ->
  loventre_global_color m = GC_green ->
  is_P_like_accessible m.

(** 2. Versioni globali (valide per tutti gli LMetrics) *)

Definition policy_never_green_on_black_hole_global : Prop :=
  forall m : LMetrics, policy_never_green_on_black_hole_pointwise m.

Definition policy_green_only_on_low_risk_non_black_hole_global : Prop :=
  forall m : LMetrics, policy_green_only_on_low_risk_non_black_hole_pointwise m.

Definition policy_borderline_green_matches_P_like_accessible_global : Prop :=
  forall m : LMetrics, policy_borderline_green_matches_P_like_accessible_pointwise m.

(** 3. Spec "ideale" complessiva della Policy *)

Definition policy_ideal_spec : Prop :=
  policy_never_green_on_black_hole_global /\
  policy_green_only_on_low_risk_non_black_hole_global /\
  policy_borderline_green_matches_P_like_accessible_global.

