(* ========================================================== *)
(*  LOVENTRE PROJECT — Loventre_Class_Separation_v3.v         *)
(*  Dicembre 2025 — Classi P_Lov / Pacc_Lov / NP_bh_Lov       *)
(*                                                            *)
(*  Obiettivo:                                                *)
(*    - introdurre le "classi Loventre" come predicati        *)
(*      su LMetrics;                                          *)
(*    - mostrare che:                                         *)
(*         ∃ m, In_NP_bh_Lov m ∧ ¬ In_Pacc_Lov m              *)
(*      cioè esiste un witness NP_like-black-hole che NON     *)
(*      appartiene alla classe P_like_accessible.             *)
(* ========================================================== *)

From Coq Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates.

From Loventre_Main Require Import
  Loventre_Phase_Separation_v3
  Loventre_Witness_v3.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================= *)
(*  1. Definizione delle classi Loventre                     *)
(* ========================================================= *)

Definition In_P_Lov (m : LMetrics) : Prop :=
  is_P_like m.

Definition In_Pacc_Lov (m : LMetrics) : Prop :=
  is_P_like_accessible m.

Definition In_NP_bh_Lov (m : LMetrics) : Prop :=
  is_NP_like_black_hole m.

(* ========================================================= *)
(*  2. Esistenza di un elemento in P_Lov                     *)
(* ========================================================= *)

Lemma Loventre_exists_P_Lov_v3 :
  exists m : LMetrics, In_P_Lov m.
Proof.
  exists m_seed11_cli_demo.
  unfold In_P_Lov.
  apply Loventre_witness_P_like_v3.
Qed.

(* ========================================================= *)
(*  3. Esistenza di un NP_bh che NON è Pacc                  *)
(* ========================================================= *)

Lemma Loventre_exists_NPbh_not_Pacc_Lov_v3 :
  exists m : LMetrics, In_NP_bh_Lov m /\ ~ In_Pacc_Lov m.
Proof.
  exists m_TSPcrit28_cli_demo.
  unfold In_NP_bh_Lov, In_Pacc_Lov.
  split.
  - apply Loventre_witness_NP_like_black_hole_v3.
  - apply Loventre_witness_NP_not_Pacc_v3.
Qed.

(* ========================================================= *)
(*  4. NP_bh_Lov NON è sotto-classe di Pacc_Lov              *)
(* ========================================================= *)

Lemma Loventre_NPbh_not_subset_Pacc_Lov_v3 :
  ~ (forall m : LMetrics, In_NP_bh_Lov m -> In_Pacc_Lov m).
Proof.
  intros Hsub.
  (* Usiamo il witness dell'esistenza precedente. *)
  destruct Loventre_exists_NPbh_not_Pacc_Lov_v3
    as [m [HNP HnotPacc]].
  specialize (Hsub m HNP).
  apply HnotPacc.
  exact Hsub.
Qed.

(* Goal di sanity locale. *)

Goal True. exact I. Qed.

