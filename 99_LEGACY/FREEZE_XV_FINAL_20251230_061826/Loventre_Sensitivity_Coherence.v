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

Module Loventre_Sensitivity_Coherence.

  Import Loventre_LMetrics.
  Import LMetrics_Robustness.
  Import Loventre_Dynamic_Perturbation.

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
    forall M : LMetrics,
      Loventre_Structural_Sensitivity.is_structurally_sensitive M ->
      exists p : Perturbation,
        ~ (
          is_structurally_stable (apply_perturbation p M) /\
          is_phase_locked (apply_perturbation p M) /\
          is_invariant (apply_perturbation p M)
        ).

End Loventre_Sensitivity_Coherence.

