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
Require Import Loventre_Class_Membership.

(**
  Alias canonici del vocabolario (A11).
*)
Module LM := Loventre_LMetrics.
Module SS := Loventre_Structural_Sensitivity.
Module NC := Loventre_Complexity_Noise_Classes.
Module CM := Loventre_Class_Membership.

(**
  Assunzione strutturale canonica:

  una metrica strutturalmente sensibile
  NON può appartenere alla classe P_STR.
*)
Parameter sensitive_excludes_PSTR :
  forall M : LM.LMetrics,
    SS.is_structurally_sensitive M ->
    ~ CM.belongs_to_class M NC.P_STR.

