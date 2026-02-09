(**
  Loventre_Sensitivity_Coherence.v
  dicembre 2025

  Micro-lemma di coerenza strutturale.

  Obiettivo:
  collegare sensibilità strutturale e risposta non uniforme
  alle perturbazioni, SENZA introdurre dinamica esplicita.

  Nessuna probabilità.
  Nessuna evoluzione temporale.
  Solo struttura logica.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_LMetrics_Robustness.
Require Import Loventre_Structural_Sensitivity.
Require Import Loventre_LMetrics_Dynamic_Perturbation.

(**
  Alias canonici del vocabolario (A11).
*)
Module LM := Loventre_LMetrics.
Module LR := LMetrics_Robustness.
Module SS := Loventre_Structural_Sensitivity.
Module DP := Loventre_Dynamic_Perturbation.

(**
  Principio di coerenza debole:

  Se una metrica è strutturalmente sensibile,
  allora esiste almeno una perturbazione che
  NON preserva simultaneamente tutte le
  proprietà strutturali canoniche.

  NOTA:
  - non specifichiamo quale proprietà fallisce
  - non costruiamo la perturbazione
  - rendiamo esplicito il limite strutturale
*)
Parameter sensitivity_breaks_uniform_coherence :
  forall M : LM.LMetrics,
    SS.is_structurally_sensitive M ->
    exists p : DP.Perturbation,
      ~ (
        LR.is_structurally_stable (DP.apply_perturbation p M) /\
        LR.is_phase_locked (DP.apply_perturbation p M) /\
        LR.is_invariant (DP.apply_perturbation p M)
      ).

