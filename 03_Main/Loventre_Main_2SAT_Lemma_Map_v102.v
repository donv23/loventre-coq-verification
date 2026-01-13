(** ********************************************************************** *)
(** Loventre_Main_2SAT_Lemma_Map_v102.v                                    *)
(**                                                                        *)
(** Catalogo ufficiale dei lemmi 2SAT certificati CANON v102.             *)
(** Nessuna nuova prova. Nessun assioma.                                   *)
(** Tutti richiamati da Geometry/Test.                                    *)
(** ********************************************************************** *)

From Loventre_Core Require Import
  Loventre_Core_Prelude.

From Loventre_Advanced Require Import
  Loventre_Class_Model
  Loventre_Class_Properties
  Loventre_SAFE_Model.

From Loventre_Advanced.Geometry Require Import
  Loventre_2SAT_EasyCrit_Compare
  Loventre_Test_Pacc_2SAT_Profile_v3
  Loventre_Test_All_2SAT.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** --------------------------------------------------------------------- *)
(** EASY Witness facts                                                     *)
(** --------------------------------------------------------------------- *)

Lemma LM_easy_in_Pacc :
  in_Pacc_Lov m_2SAT_easy_demo.
Proof. apply easy_is_Pacc. Qed.

Lemma LM_easy_safe :
  safe_loventre m_2SAT_easy_demo.
Proof. apply easy_is_SAFE. Qed.

(** --------------------------------------------------------------------- *)
(** CRITICAL Witness facts                                                 *)
(** --------------------------------------------------------------------- *)

Lemma LM_crit_not_Pacc :
  ~ in_Pacc_Lov m_2SAT_crit_demo.
Proof. apply crit_not_Pacc. Qed.

Lemma LM_crit_is_NPbh :
  in_NPbh_Lov m_2SAT_crit_demo.
Proof. apply crit_is_NPbh. Qed.

(** --------------------------------------------------------------------- *)
(** SYNTHESIS — variant without repetition                                 *)
(** --------------------------------------------------------------------- *)

Lemma LM_summary_local_2SAT_split :
  in_Pacc_Lov m_2SAT_easy_demo
  /\ safe_loventre m_2SAT_easy_demo
  /\ ~ in_Pacc_Lov m_2SAT_crit_demo
  /\ in_NPbh_Lov m_2SAT_crit_demo.
Proof.
  repeat split; try apply easy_is_Pacc; try apply easy_is_SAFE;
  try apply crit_not_Pacc; try apply crit_is_NPbh.
Qed.

(** --------------------------------------------------------------------- *)
(** FINE V102                                                             *)
(** ********************************************************************** *)

