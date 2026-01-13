(** ********************************************************************** *)
(** Loventre_Main_2SAT_Master_Test.v                                       *)
(**                                                                        *)
(** V101 — Validazione globale:                                            *)
(**   easy witness => Pacc_safe                                            *)
(**   critical witness => ¬Pacc ∧ NPbh                                     *)
(**   quindi separazione locale 2SAT                                       *)
(**                                                                        *)
(** Nessun nuovo assioma.                                                  *)
(** Nessuna dipendenza da Main esterno.                                    *)
(** ********************************************************************** *)

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
  Loventre_2SAT_LMetrics_From_JSON
  Loventre_2SAT_Decode_Compute
  Loventre_2SAT_EasyCrit_Compare
  Loventre_Test_Pacc_2SAT_Profile_v3
  Loventre_Test_All_2SAT.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** --------------------------------------------------------------------- *)
(**  Easy witness = Pacc + SAFE                                           *)
(** --------------------------------------------------------------------- *)

Lemma Easy_is_Pacc_SAFE :
  in_Pacc_Lov m_2SAT_easy_demo
  /\ safe_loventre m_2SAT_easy_demo.
Proof.
  split.
  - apply easy_is_Pacc.
  - apply easy_is_SAFE.
Qed.

(** --------------------------------------------------------------------- *)
(**  Critical witness = non-Pacc + NPbh                                   *)
(** --------------------------------------------------------------------- *)

Lemma Crit_is_not_Pacc_and_NPbh :
  ~ in_Pacc_Lov m_2SAT_crit_demo
  /\ in_NPbh_Lov m_2SAT_crit_demo.
Proof.
  split.
  - apply crit_not_Pacc.
  - apply crit_is_NPbh.
Qed.

(** --------------------------------------------------------------------- *)
(**  Test di separazione coerente                                         *)
(** --------------------------------------------------------------------- *)

Lemma Local_2SAT_Splits :
  in_Pacc_Lov m_2SAT_easy_demo
  /\ safe_loventre m_2SAT_easy_demo
  /\ ~ in_Pacc_Lov m_2SAT_crit_demo
  /\ in_NPbh_Lov m_2SAT_crit_demo.
Proof.
  repeat split.
  - apply easy_is_Pacc.
  - apply easy_is_SAFE.
  - apply crit_not_Pacc.
  - apply crit_is_NPbh.
Qed.

(** --------------------------------------------------------------------- *)
(**  FINE V101                                                            *)
(** ********************************************************************** *)

