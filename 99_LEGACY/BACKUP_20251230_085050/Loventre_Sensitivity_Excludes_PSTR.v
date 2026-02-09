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

Module Loventre_Sensitivity_Excludes_PSTR.

  Import Loventre_LMetrics.
  Import Loventre_Structural_Sensitivity.
  Import Loventre_Noise_Regimes.

  (**
    Principio canonico di esclusione:

    Una metrica strutturalmente sensibile
    NON può appartenere alla classe P_STR.
  *)
  Parameter structurally_sensitive_not_PSTR :
    forall M : LMetrics,
      is_structurally_sensitive M ->
      Loventre_Complexity_Noise_Classes.max_noise_regime_of
        Loventre_Complexity_Noise_Classes.P_STR
      <> Inert_Noise.

End Loventre_Sensitivity_Excludes_PSTR.

