(**
  Loventre_Final_Class_Separation.v
  dicembre 2025

  Capstone CANON:
  una metrica la cui sensibilità eccede P_ACC
  non può appartenere alla classe P_STR
  e viola strutturalmente i vincoli di rumore di P_ACC.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Structural_Sensitivity.
Require Import Loventre_Noise_Regimes.
Require Import Loventre_Complexity_Noise_Classes.

Require Import Loventre_Sensitivity_Exceeds_PACC.
Require Import Loventre_Sensitivity_Excludes_PSTR_Class.
Require Import Loventre_Sensitivity_Excludes_PACC.

Require Import Loventre_Class_Membership.

Module LM := Loventre_LMetrics.
Module SS := Loventre_Structural_Sensitivity.
Module NR := Loventre_Noise_Regimes.
Module NC := Loventre_Complexity_Noise_Classes.
Module EX := Loventre_Sensitivity_Exceeds_PACC.
Module EPSTR := Loventre_Sensitivity_Excludes_PSTR_Class.
Module EPACC := Loventre_Sensitivity_Excludes_PACC.
Module CM := Loventre_Class_Membership.

Theorem final_structural_violation_PACC_and_exclusion_PSTR :
  forall M : LM.LMetrics,
    EX.sensitivity_exceeds_PACC M ->
    ~ CM.belongs_to_class M NC.P_STR
    /\ (
      NC.max_noise_regime_of NC.P_ACC <> NR.Critical_Noise
    ).
Proof.
  intros M H_exceed.
  split.
  - (* esclusione P_STR *)
    apply EPSTR.sensitive_excludes_PSTR.
    exact (proj1 H_exceed).
  - (* violazione strutturale del vincolo P_ACC *)
    exact (EPACC.sensitivity_exceeding_not_PACC M H_exceed).
Qed.

