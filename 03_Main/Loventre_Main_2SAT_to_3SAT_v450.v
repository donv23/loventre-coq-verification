(***************************************************************************)
(* Loventre Main – 2SAT→3SAT Glue v450                                    *)
(* Autore: Vincenzo Loventre                                               *)
(* Modulo Main: chiama la mappa e ne attesta la consistenza                *)
(***************************************************************************)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus
  Loventre_SAFE_Model
  Loventre_Class_Model
  Loventre_Phase_Assembly
.
From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure
  Loventre_2SAT_LMetrics_Crit_JSON
  Loventre_2SAT_LMetrics_From_JSON
  Loventre_2SAT_Decode_Compute
  Loventre_2SAT_EasyCrit_Compare
  Loventre_Test_Pacc_2SAT_Profile_v3
  Loventre_Test_All_2SAT
  Loventre_Family_SAFE_BH_Frontier_v430
  Loventre_2SAT_to_3SAT_Map_v450
.

(***************************************************************************)
(* Definizione test: mappa una istanza canonica 2SAT                       *)
(* usando m_2SAT_easy_demo oppure critico                                 *)
(***************************************************************************)

Definition mapped_easy :=
  Map_2SAT_to_3SAT m_2SAT_easy_demo.

Definition mapped_crit :=
  Map_2SAT_to_3SAT m_2SAT_crit_demo.

(***************************************************************************)
(* Proprietà: SAFE preservato                                              *)
(***************************************************************************)

Lemma mapped_easy_SAFE :
  In_Safe_Loventre mapped_easy.
Proof.
  unfold mapped_easy.
  apply map_preserves_SAFE.
  apply safe_easy_demo.
Qed.

Lemma mapped_crit_SAFE :
  In_Safe_Loventre mapped_crit.
Proof.
  unfold mapped_crit.
  apply map_preserves_SAFE.
  apply safe_crit_demo.
Qed.

(***************************************************************************)
(* Proprietà: P_like preservato                                            *)
(***************************************************************************)

Lemma mapped_easy_Plike :
  In_P_like_Loventre mapped_easy.
Proof.
  unfold mapped_easy.
  apply map_preserves_P_like.
  apply Plike_easy_demo.
Qed.

Lemma mapped_crit_Plike :
  In_P_like_Loventre mapped_crit.
Proof.
  unfold mapped_crit.
  apply map_preserves_P_like.
  apply Plike_crit_demo.
Qed.

(***************************************************************************)
(* Theorem: mini backbone completo                                         *)
(***************************************************************************)

Theorem twoSAT_to_threeSAT_family_consistency_v450 :
  In_P_like_Loventre mapped_easy
  /\ In_Safe_Loventre mapped_easy
  /\ In_P_like_Loventre mapped_crit
  /\ In_Safe_Loventre mapped_crit.
Proof.
  repeat split;
    try (apply mapped_easy_Plike);
    try (apply mapped_easy_SAFE);
    try (apply mapped_crit_Plike);
    try (apply mapped_crit_SAFE).
Qed.

