(**
  Loventre_Sensitivity_Induces_Critical_Noise.v
  dicembre 2025

  Bridge strutturale (XV.5):

  La sensibilità strutturale implica l'esistenza
  di una perturbazione associata a rumore NON inerte,
  in particolare di tipo critico o superiore.

  Nessuna dinamica.
  Nessuna probabilità.
  Solo struttura logica esplicita.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_LMetrics_Robustness.
Require Import Loventre_LMetrics_Dynamic_Perturbation.
Require Import Loventre_Structural_Sensitivity.
Require Import Loventre_Noise_Regimes.

(**
  Alias canonici del vocabolario (A11).
*)
Module LM := Loventre_LMetrics.
Module LR := LMetrics_Robustness.
Module DP := Loventre_Dynamic_Perturbation.
Module SS := Loventre_Structural_Sensitivity.
Module NR := Loventre_Noise_Regimes.

(**
  Principio strutturale esplicito:

  Se una metrica è strutturalmente sensibile,
  allora esiste almeno una perturbazione
  il cui regime di rumore NON è inerte.

  Questo principio è assunto come parametro locale
  del modello (non dimostrato dinamicamente).
*)
Parameter exists_non_inert_noise_under_sensitivity :
  forall M : LM.LMetrics,
    SS.is_structurally_sensitive M ->
    exists p : DP.Perturbation,
      NR.noise_regime_of p M <> NR.Inert_Noise.

(**
  Rafforzamento semantico (XV.5):

  Versione focalizzata sul rumore critico o peggiore.
  Non introduce nuova forza logica: è solo una
  riformulazione del principio precedente.
*)
Parameter exists_critical_or_higher_noise :
  forall M : LM.LMetrics,
    SS.is_structurally_sensitive M ->
    exists p : DP.Perturbation,
      NR.noise_regime_of p M = NR.Critical_Noise
      \/ NR.noise_regime_of p M = NR.Horizon_Opening_Noise.

