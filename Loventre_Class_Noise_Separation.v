(**
  Loventre_Class_Noise_Separation.v
  dicembre 2025

  Canvas XVI-C

  Separazione strutturale delle classi Loventre
  basata sui regimi massimi di rumore ammissibile.

  Nessuna dinamica.
  Nessuna probabilità.
  Nessuna ipotesi computazionale.
*)

From Stdlib Require Import Reals.

Require Import Loventre_Noise_Regimes.
Require Import Loventre_Complexity_Noise_Classes.

Module Loventre_Class_Noise_Separation.

  (**
    Due classi sono strutturalmente distinguibili
    se ammettono regimi massimi di rumore diversi.
  *)
  Definition structurally_distinct
    (C1 C2 :
       Loventre_Complexity_Noise_Classes.Loventre_Class) : Prop :=
    Loventre_Complexity_Noise_Classes.max_noise_regime_of C1 <>
    Loventre_Complexity_Noise_Classes.max_noise_regime_of C2.

  (**
    Lemmi di separazione canonici.
    Sono conseguenze dirette degli assiomi strutturali.
  *)

  Lemma PSTR_vs_PACC_structurally_distinct :
    structurally_distinct
      Loventre_Complexity_Noise_Classes.P_STR
      Loventre_Complexity_Noise_Classes.P_ACC.
  Proof.
    unfold structurally_distinct.
    rewrite Loventre_Complexity_Noise_Classes.PSTR_noise_inert.
    rewrite Loventre_Complexity_Noise_Classes.PACC_noise_critical.
    discriminate.
  Qed.

  Lemma PACC_vs_BHNP_structurally_distinct :
    structurally_distinct
      Loventre_Complexity_Noise_Classes.P_ACC
      Loventre_Complexity_Noise_Classes.BH_NP.
  Proof.
    unfold structurally_distinct.
    rewrite Loventre_Complexity_Noise_Classes.PACC_noise_critical.
    rewrite Loventre_Complexity_Noise_Classes.BHNP_noise_horizon.
    discriminate.
  Qed.

  Lemma PSTR_vs_BHNP_structurally_distinct :
    structurally_distinct
      Loventre_Complexity_Noise_Classes.P_STR
      Loventre_Complexity_Noise_Classes.BH_NP.
  Proof.
    unfold structurally_distinct.
    rewrite Loventre_Complexity_Noise_Classes.PSTR_noise_inert.
    rewrite Loventre_Complexity_Noise_Classes.BHNP_noise_horizon.
    discriminate.
  Qed.

End Loventre_Class_Noise_Separation.

