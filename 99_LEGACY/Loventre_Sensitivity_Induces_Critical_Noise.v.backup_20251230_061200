(**
  Loventre_Sensitivity_Induces_Critical_Noise.v
  dicembre 2025

  Bridge concettuale:
  la sensibilità strutturale implica
  l'esistenza di un regime di rumore non inerte.

  Nessuna dinamica.
  Nessuna probabilità.
  Solo logica strutturale.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_LMetrics_Robustness.
Require Import Loventre_Structural_Sensitivity.
Require Import Loventre_Noise_Regimes.

Module Loventre_Sensitivity_Noise_Bridge.

  Import Loventre_LMetrics.
  Import LMetrics_Robustness.

  (**
    Principio strutturale (bridge):

    Se una metrica è strutturalmente sensibile,
    allora NON può essere soggetta solo a rumore inerte.

    NOTA IMPORTANTE:
    Questo principio NON è dimostrato costruttivamente.
    È dichiarato come parametro esplicito del modello,
    in modo onesto e controllato.
  *)
  Parameter sensitivity_excludes_inert_noise :
    forall M : LMetrics,
      Loventre_Structural_Sensitivity.is_structurally_sensitive M ->
      exists r : Loventre_Noise_Regimes.Noise_Regime,
        r <> Loventre_Noise_Regimes.Inert_Noise.

End Loventre_Sensitivity_Noise_Bridge.

