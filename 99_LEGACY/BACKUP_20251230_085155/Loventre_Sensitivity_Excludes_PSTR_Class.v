(**
  Loventre_Sensitivity_Excludes_PSTR_Class.v
  dicembre 2025

  Lemma strutturale:
  una metrica strutturalmente sensibile
  non può appartenere alla classe P_STR.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Structural_Sensitivity.
Require Import Loventre_Complexity_Noise_Classes.

Module Loventre_Sensitivity_Excludes_PSTR_Class.

  Import Loventre_LMetrics.

  (**
    Predicato di appartenenza astratto.
    Bridge semantico metriche → classi.
  *)
  Parameter belongs_to_class :
    LMetrics ->
    Loventre_Complexity_Noise_Classes.Loventre_Class ->
    Prop.

  (**
    Assunzione strutturale canonica:

    una metrica strutturalmente sensibile
    NON può appartenere alla classe P_STR.
  *)
  Parameter sensitive_excludes_PSTR :
    forall M : LMetrics,
      Loventre_Structural_Sensitivity.is_structurally_sensitive M ->
      ~ belongs_to_class
          M
          Loventre_Complexity_Noise_Classes.P_STR.

End Loventre_Sensitivity_Excludes_PSTR_Class.

