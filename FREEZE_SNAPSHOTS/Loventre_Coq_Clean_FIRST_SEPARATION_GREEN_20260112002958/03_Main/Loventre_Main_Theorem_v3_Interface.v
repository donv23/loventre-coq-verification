(** * Loventre Main Theorem v3 — Interfaccia citabile

    Questo modulo non introduce nuova matematica.
    Fornisce solo un'interfaccia "pulita" per il Main Theorem v3,
    pensata per essere citata in modo stabile nel paper LaTeX.

    In particolare definisce:

      - una proposizione citabile
          Loventre_Main_Theorem_v3_Citable_Prop

        come alias del Full Main Theorem v3,

      - un teorema citabile
          Loventre_Main_Theorem_v3_Citable

        che va da (Core Program + SAFE) a questa proposizione.
 *)

From Loventre_Main Require Import
  Loventre_Theorem_v3_Seed
  Loventre_LMetrics_Separation_Program
  Loventre_Theorem_v3_P_vs_NP_like
  Loventre_Phase_Separation_v3
  Loventre_Witness_v3
  Loventre_Class_Separation_v3
  Loventre_Mini_Theorem_P_vs_NPbh_Loventre_v3
  Loventre_Main_Theorem_v3_Bridge
  Loventre_Main_Theorem_v3
  Loventre_LMetrics_Policy_Specs.

From Loventre_Geometry Require Import
  Loventre_LMetrics_Policy_SAFE_Spec.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** ------------------------------------------------------------------ *)
(** 1. Proposizione citabile                                           *)
(** ------------------------------------------------------------------ *)

(** Proposizione "citable" del Main Theorem v3.

    Per costruzione, è semplicemente un alias del Full Main Theorem v3,
    che combina:

      - il Main Theorem v3 del Bridge;
      - l'esistenza di un NP_like-black-hole non P_like_accessible;
      - la non inclusione della classe NP_bh_Lov nella classe Pacc_Lov.

    Tutto questo è sempre interno al modello Loventre (LMetrics, SAFE, ecc.),
    e non è una dimostrazione di P≠NP classico.
 *)

Definition Loventre_Main_Theorem_v3_Citable_Prop : Prop :=
  Loventre_Main_Theorem_v3_Full_Prop.

(** ------------------------------------------------------------------ *)
(** 2. Teorema citabile                                                *)
(** ------------------------------------------------------------------ *)

(** Versione "citable" del Full Main Theorem v3:

    assumendo un Core Program e una specifica SAFE,
    otteniamo la proposizione Loventre_Main_Theorem_v3_Citable_Prop.
 *)

Theorem Loventre_Main_Theorem_v3_Citable :
  Loventre_LMetrics_Policy_Specs.Loventre_Policy_Core_Program ->
  Loventre_LMetrics_Policy_SAFE_Spec.policy_SAFE_implies_green_global ->
  Loventre_Main_Theorem_v3_Citable_Prop.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_Main_Theorem_v3_Citable_Prop.
  apply Loventre_Main_Theorem_v3_Full_from_core_and_SAFE; assumption.
Qed.

