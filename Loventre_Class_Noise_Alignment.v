(**
  Loventre_Class_Noise_Alignment.v
  dicembre 2025

  Canvas XVI-B — Allineamento strutturale
  tra classi di complessità Loventre
  e regimi qualitativi di rumore.

  Nessuna dinamica.
  Nessuna probabilità.
  Solo struttura dichiarata del modello.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Noise_Regimes.

Module Loventre_Class_Noise_Alignment.

  Import Loventre_LMetrics.
  Import Loventre_Noise_Regimes.

  (**
    Classi di complessità nel modello Loventre.
    (vocabolario canonico)
  *)
  Inductive Loventre_Class : Type :=
  | P_STR
  | P_ACC
  | BH_NP.

  (**
    Associazione strutturale:
    a ogni classe corrisponde
    il massimo regime di rumore ammissibile.

    Questa è una SCELTA DI MODELLO,
    non un teorema.
  *)
  Parameter max_noise_regime_of :
    Loventre_Class -> Noise_Regime.

  (**
    Vincoli strutturali canonici.
    Rendono esplicita la semantica del modello.
  *)
  Axiom PSTR_allows_only_inert_noise :
    max_noise_regime_of P_STR = Inert_Noise.

  Axiom PACC_allows_critical_noise :
    max_noise_regime_of P_ACC = Critical_Noise.

  Axiom BHNP_allows_horizon_noise :
    max_noise_regime_of BH_NP = Horizon_Opening_Noise.

End Loventre_Class_Noise_Alignment.

