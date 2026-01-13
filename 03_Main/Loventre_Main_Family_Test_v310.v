(**
  Loventre_Main_Family_Test_v310.v
  Famiglia 2SAT + 3SAT — test locale su 4 profili canonici
  ZERO assiomi — tutto deriva da metriche + classi + bridge
*)

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
     Loventre_Metrics_Bus
     Loventre_LMetrics_JSON_Witness.

From Loventre_Advanced.Geometry Require Import
     Loventre_Formal_Core
     Loventre_LMetrics_Phase_Predicates
     Loventre_LMetrics_Structure
     Loventre_2SAT_LMetrics_Crit_JSON
     Loventre_2SAT_LMetrics_From_JSON
     Loventre_2SAT_Decode_Compute
     Loventre_2SAT_EasyCrit_Compare
     Loventre_3SAT_LMetrics_From_JSON_v120
     Loventre_3SAT_Decode_Compute_v104
     Loventre_3SAT_SAFE_Local_v122
     Loventre_3SAT_Class_Local_v123
     Loventre_3SAT_Test_All_v124
     Loventre_2SAT3SAT_Relation_Core_v150
     Loventre_2SAT3SAT_Relation_Easy_Map_v150
     Loventre_2SAT3SAT_Relation_Crit_Map_v150
     Loventre_2SAT3SAT_Relation_Global_v150
     Loventre_2SAT3SAT_Class_Bridge_v150
     Loventre_2SAT3SAT_Mini_Theorem_v160.

From Loventre_Main Require Import
     Loventre_Main_3SAT_Aggregator_v200
     Loventre_Main_2SAT3SAT_Family_Aggregator_v300.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(***********************************************************)
(** Test Family Workplace — witness definiti e disponibili *)
(***********************************************************)

(** Alias canonici testati già negli aggregatori *)

Definition m_2SAT_easy   := m_2SAT_easy_demo.
Definition m_2SAT_crit   := m_2SAT_crit_demo.
Definition m_3SAT_easy   := m_3SAT_easy_demo.
Definition m_3SAT_crit   := m_3SAT_crit_demo.


(***********************************************************)
(** Lemmi punto-a-punto: classificazione e coerenza locale *)
(***********************************************************)

Lemma TwoSAT_easy_is_Pacc :
  In_Pacc_Lov m_2SAT_easy = true.
Proof. exact TwoSAT_easy_is_Pacc_v300. Qed.

Lemma TwoSAT_crit_is_NPbh :
  In_NP_blackhole_Lov m_2SAT_crit = true.
Proof. exact TwoSAT_crit_is_NPbh_v300. Qed.

Lemma ThreeSAT_easy_is_Pacc :
  In_Pacc_Lov m_3SAT_easy = true.
Proof. exact ThreeSAT_easy_is_Pacc_v300. Qed.

Lemma ThreeSAT_crit_is_NPbh :
  In_NP_blackhole_Lov m_3SAT_crit = true.
Proof. exact ThreeSAT_crit_is_NPbh_v300. Qed.


(***********************************************************)
(** Family Consequence — nessun assioma, solo OR e AND     *)
(***********************************************************)

Lemma Family_has_Pacc :
  exists m, In_Pacc_Lov m = true.
Proof. exists m_2SAT_easy. now rewrite TwoSAT_easy_is_Pacc. Qed.

Lemma Family_has_NPbh :
  exists m, In_NP_blackhole_Lov m = true.
Proof. exists m_3SAT_crit. now rewrite ThreeSAT_crit_is_NPbh. Qed.

Lemma Family_Pacc_and_NPbh :
  (exists m, In_Pacc_Lov m = true) /\
  (exists m, In_NP_blackhole_Lov m = true).
Proof.
  split.
  - apply Family_has_Pacc.
  - apply Family_has_NPbh.
Qed.


(***********************************************************)
(** Fine — stato conseguito: famiglia 2SAT+3SAT eterogenea *)
(***********************************************************)

(* QED v310 *)

