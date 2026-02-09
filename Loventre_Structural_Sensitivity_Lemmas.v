(**
  Loventre_Structural_Sensitivity_Lemmas.v
  dicembre 2025

  Lemmi elementari sulla sensibilità strutturale.

  Questo file rafforza il layer PSS
  senza introdurre nuove assunzioni.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_LMetrics_Robustness.
Require Import Loventre_Structural_Sensitivity.

(**
  Alias canonici del vocabolario (A11).
*)
Module LM := Loventre_LMetrics.
Module LR := LMetrics_Robustness.
Module SS := Loventre_Structural_Sensitivity.

(**
  Lemma fondamentale:
  la sensibilità strutturale implica
  la non-invarianza.

  Questo è un lemma costruttivo,
  valido per pura espansione di definizione.
*)
Lemma structurally_sensitive_not_invariant :
  forall M : LM.LMetrics,
    SS.is_structurally_sensitive M ->
    ~ LR.is_invariant M.
Proof.
  intros M H.
  unfold SS.is_structurally_sensitive in H.
  destruct H as [_ Hnot].
  exact Hnot.
Qed.

