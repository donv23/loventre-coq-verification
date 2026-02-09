(**
  Loventre_Witness_Membership_AXIS_C.v
  dicembre 2025

  AXIS C / LAB — Ponte condizionale
  dai witness (Python / JSON) a belongs_to_class.

  Questo file NON è CANON.
  Introduce assunzioni locali, auditabili.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Complexity_Noise_Classes.
Require Import Loventre_Class_Membership.

(**
  Alias canonici del vocabolario (A11)
*)
Module LM := Loventre_LMetrics.
Module NC := Loventre_Complexity_Noise_Classes.
Module CM := Loventre_Class_Membership.

(**
  Tipo astratto di witness esterni
  (es. JSON / output Python).
*)
Parameter Witness : Type.

(**
  Funzione di caricamento astratta:
  un witness determina una LMetrics.
*)
Parameter load_metrics_from_witness :
  Witness -> LM.LMetrics.

(**
  Predicato di validità del witness:
  controlli sintattici/semantici esterni.
*)
Parameter witness_valid :
  Witness -> Prop.

(**
  Assunzione LAB:
  se un witness è valido e certificato
  come appartenente a una classe C,
  allora la LMetrics caricata
  appartiene a C nel senso canonico.
*)
Parameter witness_certifies_class :
  Witness -> NC.Loventre_Class -> Prop.

Axiom witness_to_membership :
  forall (w : Witness) (C : NC.Loventre_Class),
    witness_valid w ->
    witness_certifies_class w C ->
    CM.belongs_to_class (load_metrics_from_witness w) C.

(**
  Lemma LAB di utilizzo tipico:
  un witness certificato per P_ACC
  induce appartenenza a BH_NP
  (via Mini-Teorema CANON).
*)
Require Import Loventre_Mini_Theorem_PACC_v1_CANON.

Module MT := Loventre_Mini_Theorem_PACC_v1_CANON.

Lemma witness_PACC_implies_BHNP :
  forall w : Witness,
    witness_valid w ->
    witness_certifies_class w NC.P_ACC ->
    CM.belongs_to_class
      (load_metrics_from_witness w)
      NC.BH_NP.
Proof.
  intros w Hvalid Hcert.
  apply MT.mini_theorem_PACC_in_BHNP.
  apply witness_to_membership with (w := w).
  - exact Hvalid.
  - exact Hcert.
Qed.

