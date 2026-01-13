(****************************************************)
(* LOVENTRE — MAIN AGGREGATOR 3SAT v200             *)
(* Stato CANONICO — Gennaio 2026                    *)
(* Nessun Assioma / Nessun Admitted                 *)
(* Mini–Theorem interno 3SAT (Easy/Pacc + Crit/BH)  *)
(****************************************************)

From Loventre_Core Require Import
  Loventre_Core_Prelude
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
  Loventre_Curvature_Field
  Loventre_Potential_Field
  Loventre_Barrier_Model
  Loventre_Tunneling_Model
  Loventre_Risk_From_Tunneling
  Loventre_Risk_Level
  Loventre_Risk_Level_Bridge
  Loventre_SAFE_Model
  Loventre_Class_Model
  Loventre_Class_Properties
  Loventre_Phase_Assembly
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus.

From Loventre_Advanced.Geometry Require Import
  Loventre_Formal_Core
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure
  Loventre_LMetrics_JSON_Witness
  Loventre_2SAT_LMetrics_Crit_JSON
  Loventre_2SAT_LMetrics_From_JSON
  Loventre_2SAT_Decode_Compute
  Loventre_2SAT_EasyCrit_Compare
  Loventre_2SAT3SAT_Relation_Core_v150
  Loventre_2SAT3SAT_Relation_Easy_Map_v150
  Loventre_2SAT3SAT_Relation_Crit_Map_v150
  Loventre_2SAT3SAT_Relation_Global_v150
  Loventre_2SAT3SAT_Class_Bridge_v150
  Loventre_2SAT3SAT_Mini_Theorem_v160.

(****************************************************)
(** MINI–AGGREGATORE 3SAT                           **)
(** Dichiara l'esito finale in funzione della fase **)
(****************************************************)

Section Loventre_Main_3SAT_Aggregator_v200.

  Variable m : LMetrics.

  (* Caso 3SAT ridotto che resta EASY → Pacc *)
  Lemma Loventre_3SAT_Easy_Pacc_v200 :
    is_3SAT_easy_case m ->
    In_Pacc_Lov m.
  Proof.
    intros HE.
    apply Loventre_3SAT_easy_implies_Pacc.
    exact HE.
  Qed.

  (* Caso 3SAT ridotto che è CRITICO → NP_blackhole *)
  Lemma Loventre_3SAT_Crit_NPbh_v200 :
    is_3SAT_crit_case m ->
    In_NP_bh_Lov m.
  Proof.
    intros HC.
    apply Loventre_3SAT_crit_implies_NPbh.
    exact HC.
  Qed.

  (*********************************************************)
  (** MINI–THEOREM UNIFICATO                              **)
  (**  - easy ⇒ P_accessible                              **)
  (**  - crit ⇒ NP_blackhole                              **)
  *********************************************************)

  Theorem Loventre_3SAT_Mini_Theorem_v200 :
      (is_3SAT_easy_case m -> In_Pacc_Lov m)
   /\ (is_3SAT_crit_case m -> In_NP_bh_Lov m).
  Proof.
    split.
    - apply Loventre_3SAT_Easy_Pacc_v200.
    - apply Loventre_3SAT_Crit_NPbh_v200.
  Qed.

End Loventre_Main_3SAT_Aggregator_v200.

(****************************************************)
(* EOF — v200                                       *)
(* Nessun Admitted. Nessun Assioma. Stato CANONICO. *)
(****************************************************)

