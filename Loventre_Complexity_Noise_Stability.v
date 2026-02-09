(**
  Loventre_Complexity_Noise_Stability.v
  dicembre 2025

  Canvas XVI-C

  Stabilità delle classi di complessità
  rispetto ai regimi di rumore ammessi.

  Nessuna dinamica.
  Nessuna probabilità.
  Solo coerenza strutturale.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Noise_Regimes.
Require Import Loventre_Noise_Regimes_Order.
Require Import Loventre_Complexity_Noise_Classes.

Module Loventre_Complexity_Noise_Stability.

  Import Loventre_Noise_Regimes.
  Import Loventre_Noise_Regimes_Order.

  (**
    Principio di stabilità strutturale:

    Una classe di complessità è stabile
    rispetto a ogni regime di rumore
    che rispetta il suo massimo ammissibile.
  *)
  Definition class_stable_under_noise
             (C : Loventre_Complexity_Noise_Classes.Loventre_Class)
             (r : Noise_Regime) : Prop :=
    Loventre_Complexity_Noise_Classes.respects_noise_class C r.

End Loventre_Complexity_Noise_Stability.

