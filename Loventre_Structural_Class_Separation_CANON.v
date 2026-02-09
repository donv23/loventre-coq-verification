(**
  Loventre_Structural_Class_Separation_CANON.v
  dicembre 2025

  CANON — Separazione strutturale delle classi
  tramite il bridge canonico di appartenenza.

  Nessuna dinamica.
  Nessuna probabilità.
  Nessun claim P≠NP classico.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Noise_Regimes.
Require Import Loventre_Complexity_Noise_Classes.
Require Import Loventre_Class_Membership.

(**
  Alias canonici del vocabolario (A11)
*)
Module LM := Loventre_LMetrics.
Module NR := Loventre_Noise_Regimes.
Module NC := Loventre_Complexity_Noise_Classes.
Module CM := Loventre_Class_Membership.

(**
  Inclusioni strutturali CANONICHE tra classi
  (vincoli di modello, non dimostrazioni operative).
*)
Axiom PSTR_in_PACC :
  forall M : LM.LMetrics,
    CM.belongs_to_class M NC.P_STR ->
    CM.belongs_to_class M NC.P_ACC.

Axiom PACC_in_BHNP :
  forall M : LM.LMetrics,
    CM.belongs_to_class M NC.P_ACC ->
    CM.belongs_to_class M NC.BH_NP.

(**
  Catena strutturale completa:
  P_STR ⊂ P_ACC ⊂ BH_NP
*)
Theorem structural_class_chain :
  forall M : LM.LMetrics,
    CM.belongs_to_class M NC.P_STR ->
    CM.belongs_to_class M NC.BH_NP.
Proof.
  intros M H.
  apply PACC_in_BHNP.
  apply PSTR_in_PACC.
  exact H.
Qed.

