(**
  Loventre_Phase_Transition_Threshold.v
  dicembre 2025

  Canvas XVII

  Soglia astratta di transizione di fase.
  Nessuna dinamica.
  Nessuna misura.
  Solo struttura logica.
*)

From Stdlib Require Import Reals.

Require Import Loventre_Noise_Regimes.
Require Import Loventre_Noise_Regimes_Order.
Require Import Loventre_Complexity_Noise_Classes.
Require Import Loventre_Complexity_Noise_Stability.

Module Loventre_Phase_Transition_Threshold.

  Import Loventre_Noise_Regimes.
  Import Loventre_Noise_Regimes_Order.
  Import Loventre_Complexity_Noise_Stability.

  (**
    Predicato di soglia:

    Un regime di rumore r è oltre soglia
    per una classe C se NON è ammesso
    dalla stabilità strutturale della classe.
  *)
  Definition beyond_phase_threshold
             (C : Loventre_Complexity_Noise_Classes.Loventre_Class)
             (r : Noise_Regime) : Prop :=
    ~ Loventre_Complexity_Noise_Classes.respects_noise_class C r.

  (**
    Principio astratto di transizione di fase:

    Per ogni classe di complessità,
    esiste almeno un regime di rumore
    che supera la soglia strutturale.
  *)
  Parameter exists_phase_transition_threshold :
    forall C : Loventre_Complexity_Noise_Classes.Loventre_Class,
      exists r : Noise_Regime,
        beyond_phase_threshold C r.

End Loventre_Phase_Transition_Threshold.

