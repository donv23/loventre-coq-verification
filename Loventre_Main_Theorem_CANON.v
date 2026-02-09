(**
  Loventre_Main_Theorem_CANON.v
  dicembre 2025

  Teorema principale CANON (Loventre):

  Esistono metriche che, per pura struttura,
  non appartengono a P_STR e che,
  se appartenenti a P_ACC,
  ricadono necessariamente nella regione BH_NP.

  Nessuna dinamica.
  Nessuna probabilità.
  Nessun claim P≠NP classico.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Complexity_Noise_Classes.
Require Import Loventre_Class_Membership.

Require Import Loventre_Sensitivity_Exceeds_PACC.
Require Import Loventre_Final_Class_Separation.
Require Import Loventre_Mini_Theorem_PACC_v1_CANON.

Module LM := Loventre_LMetrics.
Module NC := Loventre_Complexity_Noise_Classes.
Module CM := Loventre_Class_Membership.
Module EX := Loventre_Sensitivity_Exceeds_PACC.

Theorem Loventre_Main_Theorem_CANON :
  exists M : LM.LMetrics,
    ~ CM.belongs_to_class M NC.P_STR
    /\ (
      CM.belongs_to_class M NC.P_ACC ->
      CM.belongs_to_class M NC.BH_NP
    ).
Proof.
  destruct EX.exists_sensitivity_exceeding_PACC as [M H_exceed].

  destruct
    (final_structural_violation_PACC_and_exclusion_PSTR M H_exceed)
    as [H_not_PSTR H_violate_PACC].

  exists M.
  split.
  - exact H_not_PSTR.
  - (* se M ∈ P_ACC allora M ∈ BH_NP *)
    apply mini_theorem_PACC_in_BHNP.
Qed.

