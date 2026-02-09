(**
  Loventre_Main_Theorem_v3_AXIS_C.v
  dicembre 2025

  AXIS C / LAB — Wrapper principale.

  Integra:
  - Mini-teoremi CANON sulle classi
  - Ponte LAB witness → belongs_to_class

  Nessuna modifica al CANON.
  Tutte le assunzioni restano localizzate in Axis C.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Complexity_Noise_Classes.
Require Import Loventre_Class_Membership.

(* Mini-teoremi CANON *)
Require Import Loventre_Structural_Class_Separation_CANON.
Require Import Loventre_Mini_Theorem_PACC_v1_CANON.

(* Ponte LAB *)
Require Import Loventre_Witness_Membership_AXIS_C.

Module LM := Loventre_LMetrics.
Module NC := Loventre_Complexity_Noise_Classes.
Module CM := Loventre_Class_Membership.
Module SEP := Loventre_Structural_Class_Separation_CANON.
Module MT := Loventre_Mini_Theorem_PACC_v1_CANON.
Module WM := Loventre_Witness_Membership_AXIS_C.

(**
  MAIN THEOREM (Axis C, condizionale):

  Se esiste un witness valido che certifica
  appartenenza a P_ACC, allora la metrica
  associata appartiene a BH_NP.

  Questo è il punto di arrivo operativo:
  - i witness (Python/JSON) attivano il risultato
  - la separazione è quella del CANON
*)
Theorem main_theorem_witness_PACC_implies_BHNP :
  forall w : WM.Witness,
    WM.witness_valid w ->
    WM.witness_certifies_class w NC.P_ACC ->
    CM.belongs_to_class
      (WM.load_metrics_from_witness w)
      NC.BH_NP.
Proof.
  intros w Hvalid Hcert.
  apply MT.mini_theorem_PACC_in_BHNP.
  apply WM.witness_to_membership with (w := w).
  - exact Hvalid.
  - exact Hcert.
Qed.

(**
  Corollario strutturale (Axis C):

  Qualunque pipeline esterna che produca
  un witness valido in P_ACC produce
  automaticamente un caso BH_NP
  nel modello Loventre.
*)
Corollary external_pipeline_forces_BHNP :
  forall w : WM.Witness,
    WM.witness_valid w ->
    WM.witness_certifies_class w NC.P_ACC ->
    exists M : LM.LMetrics,
      M = WM.load_metrics_from_witness w /\
      CM.belongs_to_class M NC.BH_NP.
Proof.
  intros w Hvalid Hcert.
  exists (WM.load_metrics_from_witness w).
  split.
  - reflexivity.
  - apply main_theorem_witness_PACC_implies_BHNP; assumption.
Qed.

