(**
  Loventre_Complexity_Noise_Classes.v
  dicembre 2025

  Canvas XVI-B

  Classi di complessità come regioni
  nell'ordine strutturale dei regimi di rumore.

  Nessuna dinamica.
  Nessuna probabilità.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Structural_Sensitivity.
Require Import Loventre_Noise_Regimes.
Require Import Loventre_Noise_Regimes_Order.

Module Loventre_Complexity_Noise_Classes.

  Import Loventre_LMetrics.
  Import Loventre_Noise_Regimes.
  Import Loventre_Noise_Regimes_Order.

  (**
    Classi di complessità Loventre (astratte).
  *)
  Inductive Loventre_Class : Type :=
  | P_STR
  | P_ACC
  | BH_NP.

  (**
    Associazione strutturale minima:
    a ogni classe corrisponde un regime
    di rumore massimo ammissibile.
  *)
  Parameter max_noise_regime_of :
    Loventre_Class -> Noise_Regime.

  (**
    Vincoli strutturali canonici.
    Questi fissano il modello, non lo dimostrano.
  *)
  Axiom PSTR_noise_inert :
    max_noise_regime_of P_STR = Inert_Noise.

  Axiom PACC_noise_critical :
    max_noise_regime_of P_ACC = Critical_Noise.

  Axiom BHNP_noise_horizon :
    max_noise_regime_of BH_NP = Horizon_Opening_Noise.

  (**
    Interpretazione strutturale:
    una classe ammette solo rumore
    minore o uguale al proprio massimo.
  *)
  Definition respects_noise_class
             (C : Loventre_Class)
             (r : Noise_Regime) : Prop :=
    Loventre_Noise_Regimes_Order.noise_precedes r (max_noise_regime_of C)
    \/ r = max_noise_regime_of C.

End Loventre_Complexity_Noise_Classes.

