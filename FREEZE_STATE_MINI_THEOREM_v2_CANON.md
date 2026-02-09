(**
  Loventre_Mini_Theorem_PACC_v1_CANON.v
  dicembre 2025

  MINI-TEOREMA CANONICO (P_ACC)

  Separazione strutturale interna al modello Loventre:
  una metrica appartenente a P_ACC
  appartiene necessariamente a BH_NP.

  Nessuna dinamica.
  Nessuna probabilità.
  Nessun claim P≠NP classico.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Complexity_Noise_Classes.
Require Import Loventre_Class_Membership.
Require Import Loventre_Structural_Class_Separation_CANON.

(**
  Alias canonici del vocabolario (A11)
*)
Module LM := Loventre_LMetrics.
Module NC := Loventre_Complexity_Noise_Classes.
Module CM := Loventre_Class_Membership.
Module SC := Loventre_Structural_Class_Separation_CANON.

(**
  Mini-teorema:
  P_ACC ⊂ BH_NP (nel modello Loventre)
*)
Theorem mini_theorem_PACC_in_BHNP :
  forall M : LM.LMetrics,
    CM.belongs_to_class M NC.P_ACC ->
    CM.belongs_to_class M NC.BH_NP.
Proof.
  intros M H.
  apply SC.PACC_in_BHNP.
  exact H.
Qed.

