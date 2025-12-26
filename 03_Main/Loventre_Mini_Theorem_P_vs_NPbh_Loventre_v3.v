(* ========================================================== *)
(*  LOVENTRE PROJECT — Loventre_Mini_Theorem_P_vs_NPbh_v3     *)
(*                                                            *)
(*  Dicembre 2025 — Mini Teorema P_vs_NP_bh (Loventre v3)     *)
(*                                                            *)
(*  Idea:                                                     *)
(*    Nel paesaggio LMetrics definiamo le classi:             *)
(*      - In_P_Lov (fase P_like)                             *)
(*      - In_Pacc_Lov (fase P_like_accessible)               *)
(*      - In_NP_bh_Lov (fase NP_like-black-hole)             *)
(*                                                            *)
(*    Usando i lemma di witness e di separazione di classe,  *)
(*    otteniamo due enunciati compatti:                       *)
(*                                                            *)
(*      1) esiste un witness m in In_NP_bh_Lov che NON è     *)
(*         in In_Pacc_Lov;                                   *)
(*      2) quindi NP_bh_Lov NON è sotto-classe di Pacc_Lov.  *)
(*                                                            *)
(*  NOTA: Questo è un teorema interno al modello Loventre;   *)
(*        non va confuso con P!=NP classico.                 *)
(* ========================================================== *)

From Coq Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates.

From Loventre_Main Require Import
  Loventre_Class_Separation_v3.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================= *)
(*  1. Enunciati compatti del mini-teorema                   *)
(* ========================================================= *)

Definition Loventre_P_vs_NPbh_Loventre_v3_exists_Prop : Prop :=
  exists m : LMetrics, In_NP_bh_Lov m /\ ~ In_Pacc_Lov m.

Definition Loventre_P_vs_NPbh_Loventre_v3_nonsubset_Prop : Prop :=
  ~ (forall m : LMetrics, In_NP_bh_Lov m -> In_Pacc_Lov m).

(* ========================================================= *)
(*  2. Teoremi v3 (alias dei lemma di separazione di classe) *)
(* ========================================================= *)

Theorem Loventre_P_vs_NPbh_Loventre_v3_exists :
  Loventre_P_vs_NPbh_Loventre_v3_exists_Prop.
Proof.
  unfold Loventre_P_vs_NPbh_Loventre_v3_exists_Prop.
  apply Loventre_exists_NPbh_not_Pacc_Lov_v3.
Qed.

Theorem Loventre_P_vs_NPbh_Loventre_v3_nonsubset :
  Loventre_P_vs_NPbh_Loventre_v3_nonsubset_Prop.
Proof.
  unfold Loventre_P_vs_NPbh_Loventre_v3_nonsubset_Prop.
  apply Loventre_NPbh_not_subset_Pacc_Lov_v3.
Qed.

(* Goal di sanity locale. *)

Goal True. exact I. Qed.

