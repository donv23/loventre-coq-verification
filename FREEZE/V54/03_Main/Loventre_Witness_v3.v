From Stdlib Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates.

From Loventre_Main Require Import
  Loventre_Phase_Separation_v3.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Lemma Loventre_witness_P_like_v3 :
  is_P_like m_seed11_cli_demo.
Proof.
  apply m_seed11_soddisfa_is_P_like.
Qed.

Lemma Loventre_witness_NP_like_black_hole_v3 :
  is_NP_like_black_hole m_TSPcrit28_cli_demo.
Proof.
  apply m_TSPcrit28_soddisfa_is_NP_like_black_hole.
Qed.

Lemma Loventre_witness_NP_not_Pacc_v3 :
  ~ is_P_like_accessible m_TSPcrit28_cli_demo.
Proof.
  apply Loventre_NP_like_black_hole_not_P_like_accessible_v3.
  apply Loventre_witness_NP_like_black_hole_v3.
Qed.

Goal True. exact I. Qed.

