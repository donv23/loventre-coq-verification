(** Loventre_Main_Prelude.v
    V57 — Prelude consolidato con re-export di LMetrics
 *)

From Stdlib Require Import Bool Reals ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Time
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy
  Loventre_Foundation_Logic
  Loventre_Foundation_Measures
  Loventre_Foundation_Complexity.

From Loventre_Advanced Require Import
  Loventre_Geometry_Core
  Loventre_Geometry_Measure
  Loventre_Curvature_Core
  Loventre_Curvature_Potential
  Loventre_Curvature_Entropy
  Loventre_Curvature_Flow
  Loventre_Regime_Core
  Loventre_Regime_Discrete
  Loventre_Regime_Continuous
  Loventre_Regime_Thresholds
  Loventre_Complexity_UpperBounds
  Loventre_Complexity_Criticality
  Loventre_LMetrics_Core.

Export Loventre_LMetrics_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

