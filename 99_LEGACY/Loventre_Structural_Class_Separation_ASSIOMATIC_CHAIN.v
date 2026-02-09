(**
  Loventre_Structural_Class_Separation.v
  dicembre 2025

  Canvas XVI-A

  Separazione strutturale delle classi di complessità
  nel modello di Loventre.

  Nessuna dinamica.
  Nessuna probabilità.
  Nessun claim P≠NP classico.
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Structural_Sensitivity.
Require Import Loventre_Sensitivity_Excludes_PSTR.
Require Import Loventre_Noise_Regimes.
Require Import Loventre_Noise_Regimes_Order.
Require Import Loventre_Complexity_Noise_Classes.

Module Loventre_Structural_Class_Separation.

  Import Loventre_LMetrics.
  Import Loventre_Noise_Regimes.
  Import Loventre_Noise_Regimes_Order.

  (**
    Interpretazione strutturale minimale:

    Una metrica appartiene a una classe C
    se il massimo regime di rumore che ammette
    è compatibile con la classe.
  *)
  Definition belongs_to_class
             (M : LMetrics)
             (C : Loventre_Complexity_Noise_Classes.Loventre_Class) : Prop :=
    exists r : Noise_Regime,
      Loventre_Complexity_Noise_Classes.respects_noise_class C r.

  (**
    Inclusione strutturale:
    P_STR ⊂ P_ACC
  *)
  Axiom PSTR_in_PACC :
    forall M : LMetrics,
      belongs_to_class M
        Loventre_Complexity_Noise_Classes.P_STR ->
      belongs_to_class M
        Loventre_Complexity_Noise_Classes.P_ACC.

  (**
    Inclusione strutturale:
    P_ACC ⊂ BH_NP
  *)
  Axiom PACC_in_BHNP :
    forall M : LMetrics,
      belongs_to_class M
        Loventre_Complexity_Noise_Classes.P_ACC ->
      belongs_to_class M
        Loventre_Complexity_Noise_Classes.BH_NP.

  (**
    Catena strutturale completa:
    P_STR ⊂ P_ACC ⊂ BH_NP
  *)
  Theorem structural_class_chain :
    forall M : LMetrics,
      belongs_to_class M
        Loventre_Complexity_Noise_Classes.P_STR ->
      belongs_to_class M
        Loventre_Complexity_Noise_Classes.BH_NP.
  Proof.
    intros M HP.
    apply PACC_in_BHNP.
    apply PSTR_in_PACC.
    exact HP.
  Qed.

End Loventre_Structural_Class_Separation.

