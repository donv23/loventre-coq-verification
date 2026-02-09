(**
  Loventre_Complexity_Noise_Classes.v
  gennaio 2026

  Wrapper canonico per allineare:
   - classi Loventre
   - massimo regime di rumore ammesso
*)

From Stdlib Require Import Reals.

Require Import Loventre_Noise_Regimes.

Module Loventre_Complexity_Noise_Classes.

  Import Loventre_Noise_Regimes.

  (**
    Classi canonicamente definite
  *)
  Inductive Loventre_Class : Type :=
  | P_STR
  | P_ACC
  | BH_NP.

  (**
    Mappa canonica massima ammessa
  *)
  Parameter max_noise_regime_of :
    Loventre_Class -> Noise_Regime.

  (**
    Axiomi di modello (uguali a Alignment)
  *)

  Parameter PSTR_noise_inert :
    max_noise_regime_of P_STR = Inert_Noise.

  Parameter PACC_noise_critical :
    max_noise_regime_of P_ACC = Critical_Noise.

  Parameter BHNP_noise_horizon :
    max_noise_regime_of BH_NP = Horizon_Opening_Noise.

  (**
    Relazione "rispettato da"
    una classe rispetta un regime se non lo supera
  *)
  Definition respects_noise_class
             (C : Loventre_Class)
             (r : Noise_Regime) : Prop :=
    match C with
    | P_STR =>
        r = Inert_Noise
    | P_ACC =>
        r = Inert_Noise \/ r = Critical_Noise
    | BH_NP =>
        True
    end.

End Loventre_Complexity_Noise_Classes.

