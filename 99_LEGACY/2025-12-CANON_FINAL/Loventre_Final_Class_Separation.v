(**
  Loventre_Final_Class_Separation.v
  dicembre 2025

  Capstone CANON:
  separazione strutturale finale per esclusione.

  Nessun nuovo concetto.
  Solo composizione di risultati già verificati.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Structural_Sensitivity.
Require Import Loventre_Noise_Regimes.
Require Import Loventre_Complexity_Noise_Classes.
Require Import Loventre_Sensitivity_Exceeds_PACC.
Require Import Loventre_Sensitivity_Excludes_PACC.
Require Import Loventre_Sensitivity_Excludes_PSTR_Class.

Module Loventre_Final_Class_Separation.

  (** Alias canonici *)
  Module LM := Loventre_LMetrics.
  Module SS := Loventre_Structural_Sensitivity.
  Module NR := Loventre_Noise_Regimes.
  Module NC := Loventre_Complexity_Noise_Classes.
  Module EX := Loventre_Sensitivity_Exceeds_PACC.
  Module EPACC := Loventre_Sensitivity_Excludes_PACC.
  Module EPSTR := Loventre_Sensitivity_Excludes_PSTR_Class.

  (**
    Teorema finale di esclusione strutturale.
  *)
  Theorem final_structural_exclusion :
    exists M : LM.LMetrics,
      EX.sensitivity_exceeds_PACC M /\
      ~ EPSTR.belongs_to_class M NC.P_STR /\
      (EX.sensitivity_exceeds_PACC M ->
       NC.max_noise_regime_of NC.P_ACC <> NR.Critical_Noise).
  Proof.
    destruct EX.exists_sensitivity_exceeding_PACC as [M HM].
    exists M.
    split.
    - exact HM.
    - split.
      + apply EPSTR.sensitive_excludes_PSTR.
        exact (proj1 HM).
      + intro H.
        exact (EPACC.sensitivity_exceeding_not_PACC M H).
  Qed.

End Loventre_Final_Class_Separation.

