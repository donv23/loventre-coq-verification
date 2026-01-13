(**
  Loventre_Main_Family_Class_Safe_Bridge_v360.v
  Punto logico chiave:
  SAFE(m) se e solo se is_P_accessible(m)
  NON SAFE(m) se e solo se is_NP_blackhole(m)
  per {2SAT easy/demo, 3SAT demo/crit}
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_LMetrics_Phase_Predicates
     Loventre_SAFE_Model
     Loventre_Class_Model
     Loventre_LMetrics_JSON_Witness.
From Loventre_Advanced.Geometry Require Import
       Loventre_Family_SAFE_Bridge_v330
       Loventre_Family_UNSAFE_Bridge_v340.

Module Loventre_Main_Family_Class_Safe_Bridge_V360.

(** ---- Implicazioni già note (V330 e V340) ---- *)
Lemma Pacc_implies_SAFE m :
  is_P_accessible m = true ->
  SAFE_condition m = true.
Proof.
  apply Loventre_Family_SAFEBRIDGE_V330.Pacc_implies_SAFE.
Qed.

Lemma NPbh_implies_not_SAFE m :
  is_NP_blackhole m = true ->
  SAFE_condition m = false.
Proof.
  apply Loventre_Family_UNSAFEBRIDGE_V340.NPbh_implies_not_SAFE.
Qed.

(** ---- Implicazioni inverse: SAFE m = true -> P_acc m ---- *)
Lemma SAFE_true_implies_Pacc_2SAT_easy :
  SAFE_condition m_2SAT_easy_demo = true ->
  is_P_accessible m_2SAT_easy_demo = true.
Proof.
  intro Hs.
  exact m_2SAT_easy_is_Pacc.
Qed.

Lemma SAFE_true_implies_Pacc_3SAT_demo :
  SAFE_condition m_3SAT_demo = true ->
  is_P_accessible m_3SAT_demo = true.
Proof.
  intro Hs.
  exact m_3SAT_demo_is_Pacc.
Qed.

(** ---- SAFE false -> NP_blackhole ---- *)
Lemma SAFE_false_implies_NPbh_2SAT_crit :
  SAFE_condition m_2SAT_crit_demo = false ->
  is_NP_blackhole m_2SAT_crit_demo = true.
Proof.
  intro Hs.
  exact m_2SAT_crit_is_NPbh.
Qed.

Lemma SAFE_false_implies_NPbh_3SAT_crit :
  SAFE_condition m_3SAT_crit_demo = false ->
  is_NP_blackhole m_3SAT_crit_demo = true.
Proof.
  intro Hs.
  exact m_3SAT_crit_is_NPbh.
Qed.

(** ---- Roundtrip riassuntivo su tutta la famiglia ---- *)
Lemma Family_roundtrip_summary :
     (SAFE_condition m_2SAT_easy_demo = true
      <-> is_P_accessible m_2SAT_easy_demo = true)
  /\ (SAFE_condition m_3SAT_demo = true
      <-> is_P_accessible m_3SAT_demo = true)
  /\ (SAFE_condition m_2SAT_crit_demo = false
      <-> is_NP_blackhole m_2SAT_crit_demo = true)
  /\ (SAFE_condition m_3SAT_crit_demo = false
      <-> is_NP_blackhole m_3SAT_crit_demo = true).
Proof.
  repeat split; try split;
    try apply TwoSAT_easy_is_SAFE;
    try apply ThreeSAT_demo_is_SAFE;
    try apply TwoSAT_crit_not_SAFE;
    try apply ThreeSAT_crit_not_SAFE;
    try apply SAFE_true_implies_Pacc_2SAT_easy;
    try apply SAFE_true_implies_Pacc_3SAT_demo;
    try apply SAFE_false_implies_NPbh_2SAT_crit;
    try apply SAFE_false_implies_NPbh_3SAT_crit.
Qed.

End Loventre_Main_Family_Class_Safe_Bridge_V360.

