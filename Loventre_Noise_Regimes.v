(**
  Loventre_Noise_Regimes.v

  Canonical Vocabulary Layer — Noise Regimes

  Purpose:
  Introduce a qualitative classification of structural noise
  without assuming any dynamic or probabilistic structure.

  This file defines *only vocabulary*.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_LMetrics_Dynamic_Perturbation.

(**
  Qualitative regimes of structural noise.

  This is a descriptive taxonomy only.
*)
Inductive Noise_Regime : Type :=
| Inert_Noise
| Critical_Noise
| Horizon_Opening_Noise.

(**
  Association of a perturbation with a noise regime
  relative to a given metric configuration.

  No properties are assumed.
*)
Parameter noise_regime_of :
  Loventre_Dynamic_Perturbation.Perturbation ->
  Loventre_LMetrics.LMetrics ->
  Noise_Regime.

(**
  Informal interpretation predicates.

  These predicates are intentionally left undefined
  and serve only as placeholders for future semantics.
*)
Definition is_inert_noise
           (p : Loventre_Dynamic_Perturbation.Perturbation)
           (M : Loventre_LMetrics.LMetrics) : Prop :=
  noise_regime_of p M = Inert_Noise.

Definition is_critical_noise
           (p : Loventre_Dynamic_Perturbation.Perturbation)
           (M : Loventre_LMetrics.LMetrics) : Prop :=
  noise_regime_of p M = Critical_Noise.

Definition is_horizon_opening_noise
           (p : Loventre_Dynamic_Perturbation.Perturbation)
           (M : Loventre_LMetrics.LMetrics) : Prop :=
  noise_regime_of p M = Horizon_Opening_Noise.

