(**
  Loventre_Sensitivity_Excludes_PSTR.v
  dicembre 2025

  Canvas XVI-D

  Principio strutturale:
  la sensibilità strutturale esclude
  l'appartenenza alla classe P_STR.

  Questo è un vincolo di modello,
  non un teorema derivato.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Structural_Sensitivity.
Require Import Loventre_Noise_Regimes.
Require Import Loventre_Complexity_Noise_Classes.

(**
  Alias canonici del vocabolario (A11).
*)
Module LM := Loventre_LMetrics.
Module SS := Loventre_Structural_Sensitivity.
Module NR := Loventre_Noise_Regimes.
Module NC := Loventre_Complexity_Noise_Classes.

(**
  Principio canonico di esclusione:

  Una metrica strutturalmente sensibile
  NON può appartenere alla classe P_STR.
*)
Parameter structurally_sensitive_not_PSTR :
  forall M : LM.LMetrics,
    SS.is_structurally_sensitive M ->
    NC.max_noise_regime_of NC.P_STR
    <> NR.Inert_Noise.

