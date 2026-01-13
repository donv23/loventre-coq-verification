(**  ***************************************************************  **)
(**      Loventre Project — Geometry Layer — V85 Class Bridge        **)
(**      CANON FILE — NO ASSIOMS — NO 03_Main                        **)
(**      Autore: Vincenzo Loventre + ChatGPT                         **)
(**      Stato: V85.1 — Bridge Pacc → Classi locali                  **)
(**  ***************************************************************  **)

From Coq Require Import Bool.Bool.

From Loventre_Core Require Import Loventre_LMetrics.

From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Phase_Predicates
     Loventre_2SAT_Pacc_Monotonicity
     Loventre_2SAT_Pacc_Lemma
     Loventre_2SAT_Phase_Separation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_2SAT_Pacc_Class_Bridge.

  (** ------------------------------------------------------------ *)
  (** 1. Classi locali basate su metriche                           *)
  (** ------------------------------------------------------------ *)

  (** Classe locale “Pacc_Lov” — vive unicamente nel Geometry layer *)
  Definition in_Pacc_Lov_local (m : LMetrics) : Prop :=
    is_pacc_2sat m = true.

  (** Classe locale “NPbh_Lov” — semplicemente negazione di Pacc   *)
  Definition in_NPbh_Lov_local (m : LMetrics) : Prop :=
    is_pacc_2sat m = false.

  (** ------------------------------------------------------------ *)
  (** 2. Witness easy/crit già introdotti nel layer precedente      *)
  (** ------------------------------------------------------------ *)

  Parameter m_2sat_easy   : LMetrics.
  Parameter m_2sat_crit   : LMetrics.

  Hypothesis easy_is_pacc :
      is_pacc_2sat m_2sat_easy = true.

  Hypothesis crit_is_not_pacc :
      is_pacc_2sat m_2sat_crit = false.

  (** ------------------------------------------------------------ *)
  (** 3. Lemmi di appartenenza alle classi                          *)
  (** ------------------------------------------------------------ *)

  Lemma easy_in_Pacc_Lov :
      in_Pacc_Lov_local m_2sat_easy.
  Proof.
    unfold in_Pacc_Lov_local; rewrite easy_is_pacc; reflexivity.
  Qed.

  Lemma crit_in_NPbh_Lov :
      in_NPbh_Lov_local m_2sat_crit.
  Proof.
    unfold in_NPbh_Lov_local; rewrite crit_is_not_pacc; reflexivity.
  Qed.

  (** ------------------------------------------------------------ *)
  (** 4. Prima distinzione di classi nel layer Geometry             *)
  (** ------------------------------------------------------------ *)

  Theorem class_distinction_2sat_local :
      in_Pacc_Lov_local m_2sat_easy
   /\ in_NPbh_Lov_local m_2sat_crit.
  Proof.
    split; [apply easy_in_Pacc_Lov | apply crit_in_NPbh_Lov].
  Qed.

End Loventre_2SAT_Pacc_Class_Bridge.

