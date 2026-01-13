(*
   Loventre_Main_3SAT_Local_Aggregator_v140.v
   CANVAS 3 — Aggregatore Coerente Locale (3SAT)
   Nessun assioma nuovo. Nessun Admitted.
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_SAFE_Model
     Loventre_Class_Model
     Loventre_Phase_Assembly.

From Loventre_Advanced.Geometry Require Import
  Loventre_Formal_Core
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure
  Loventre_3SAT_LMetrics_From_JSON_v120
  Loventre_3SAT_Decode_Compute_v104
  Loventre_3SAT_SAFE_Local_v122
  Loventre_3SAT_Class_Local_v123
  Loventre_3SAT_EasyCrit_Compare_v121
  Loventre_3SAT_Test_All_v124
  Loventre_3SAT_Mini_Local_Theorem_v130.

Set Implicit Arguments.
Set Asymmetric Patterns.

Module Loventre_Main_3SAT_Local_Aggregator_v140.

(** Import the two canonical 3SAT points *)
Definition m3_easy : LMetrics := m_3sat_easy_demo.
Definition m3_crit : LMetrics := m_3sat_crit_demo.

(** The core separation result:
    easy sector is Pacc, critical is NPbh *)
Theorem local_separation_easy_crit :
  (In_Pacc_Lov m3_easy) /\
  (~ In_Pacc_Lov m3_crit) /\
  (In_NPbh_Lov m3_crit).
Proof.
  split.
  - apply pacc_easy.
  - split.
    + apply not_pacc_crit.
    + apply npbh_crit.
Qed.

(** Logical "corollary": Pacc and NPbh cannot coincide locally *)
Theorem no_collapse_Pacc_NPbh :
  forall m : LMetrics,
    In_Pacc_Lov m -> In_NPbh_Lov m -> False.
Proof.
  intros m HP HNP.
  unfold In_Pacc_Lov, In_NPbh_Lov in *.
  destruct HP as [safeP _].
  destruct HNP as [_ notSafe].
  contradiction.
Qed.

(** Showcase: applying collapse guard to the critical point *)
Theorem crit_is_not_pacc :
  In_NPbh_Lov m3_crit -> ~ In_Pacc_Lov m3_crit.
Proof.
  intros H.
  intro H2.
  apply (no_collapse_Pacc_NPbh m3_crit).
  exact H2.
  exact H.
Qed.

Print local_separation_easy_crit.
Print no_collapse_Pacc_NPbh.
Print crit_is_not_pacc.

End Loventre_Main_3SAT_Local_Aggregator_v140.

