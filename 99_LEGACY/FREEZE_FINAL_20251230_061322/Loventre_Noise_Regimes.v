(**
  Loventre_Noise_Regimes.v

  Exploratory Layer — Noise Regimes (Skeleton v0)

  Purpose:
  Introduce a qualitative classification of structural noise
  without assuming any dynamic or probabilistic structure.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Global_Invariant_Stub.
Require Import Loventre_LMetrics_Dynamic_Perturbation.

Import Loventre_LMetrics.
Import Loventre_Global_Invariant.
Import Loventre_Dynamic_Perturbation.

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
  Perturbation -> LMetrics -> Noise_Regime.

(**
  Informal interpretation predicates.

  These predicates are intentionally left undefined
  and serve only as placeholders for future semantics.
*)
Definition is_inert_noise
           (p : Perturbation) (M : LMetrics) : Prop :=
  noise_regime_of p M = Inert_Noise.

Definition is_critical_noise
           (p : Perturbation) (M : LMetrics) : Prop :=
  noise_regime_of p M = Critical_Noise.

Definition is_horizon_opening_noise
           (p : Perturbation) (M : LMetrics) : Prop :=
  noise_regime_of p M = Horizon_Opening_Noise.

