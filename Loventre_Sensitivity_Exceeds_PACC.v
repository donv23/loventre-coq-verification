(**
  Loventre_Sensitivity_Exceeds_PACC.v
  dicembre 2025

  Soglia strutturale:
  esistono forme di sensibilità
  che non possono essere confinate
  entro il regime P_ACC.
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
  Definizione minimale:
  una sensibilità è "oltre P_ACC"
  se ammette un regime di rumore
  non consentito da P_ACC.
*)
Definition sensitivity_exceeds_PACC (M : LM.LMetrics) : Prop :=
  SS.is_structurally_sensitive M /\
  exists r : NR.Noise_Regime,
    r <> NR.Critical_Noise /\
    r <> NR.Inert_Noise.

(**
  Assunzione strutturale controllata:

  esiste almeno una metrica
  la cui sensibilità eccede P_ACC.
*)
Parameter exists_sensitivity_exceeding_PACC :
  exists M : LM.LMetrics,
    sensitivity_exceeds_PACC M.

