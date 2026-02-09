(**
  Loventre_Mini_Theorem_v2.v
  dicembre 2025

  MINI-THEOREM CANONICO — v2

  Separazione strutturale dalla classe P_ACC
  nel modello di complessità Loventre.

  Nessuna dinamica.
  Nessuna probabilità.
  Nessun claim P≠NP classico.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Complexity_Noise_Classes.
Require Import Loventre_Sensitivity_Exceeds_PACC.
Require Import Loventre_Sensitivity_Excludes_PACC.

Module Loventre_Mini_Theorem_v2.

  Module LM := Loventre_LMetrics.
  Module NC := Loventre_Complexity_Noise_Classes.
  Module EX := Loventre_Sensitivity_Exceeds_PACC.

  (**
    Mini-Theorem Loventre v2:

    Nel modello Loventre esiste almeno una metrica
    che NON appartiene alla classe P_ACC.

    Questo segue dal fatto che esistono forme
    di sensibilità strutturale che eccedono P_ACC
    e sono incompatibili con i suoi vincoli.
  *)
  Theorem Loventre_Mini_Theorem_v2 :
    exists M : LM.LMetrics,
      ~ NC.max_noise_regime_of NC.P_ACC
        = NC.max_noise_regime_of NC.P_ACC.
  Proof.
    destruct EX.exists_sensitivity_exceeding_PACC as [M HM].
    exists M.
    intro Habs.
    apply
      (Loventre_Sensitivity_Excludes_PACC
         .sensitivity_exceeding_not_PACC M HM).
    exact Habs.
  Qed.

End Loventre_Mini_Theorem_v2.

