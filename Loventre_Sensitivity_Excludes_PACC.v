(**
  Loventre_Sensitivity_Excludes_PACC.v
  dicembre 2025

  Principio strutturale:
  una sensibilità che eccede P_ACC
  esclude l’appartenenza a P_ACC.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Structural_Sensitivity.
Require Import Loventre_Noise_Regimes.
Require Import Loventre_Complexity_Noise_Classes.
Require Import Loventre_Sensitivity_Exceeds_PACC.

(**
  Alias canonici del vocabolario (A11).
*)
Module LM := Loventre_LMetrics.
Module SS := Loventre_Structural_Sensitivity.
Module NR := Loventre_Noise_Regimes.
Module NC := Loventre_Complexity_Noise_Classes.
Module EX := Loventre_Sensitivity_Exceeds_PACC.

(**
  Assioma di esclusione strutturale.

  P_ACC ammette al massimo rumore critico.
  Una sensibilità che eccede P_ACC
  è incompatibile con questo vincolo.
*)
Parameter sensitivity_exceeding_not_PACC :
  forall M : LM.LMetrics,
    EX.sensitivity_exceeds_PACC M ->
    ~ (
      NC.max_noise_regime_of NC.P_ACC
      = NR.Critical_Noise
    ).

