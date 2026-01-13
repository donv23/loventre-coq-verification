(**  ***************************************************************  **)
(**      Loventre Project — Geometry Layer — V86 SAFE Bridge        **)
(**      CANON FILE — NO ASSIOMS — NO 03_Main                        **)
(**      Autore: Vincenzo Loventre + ChatGPT                         **)
(**      Stato: V86 — SAFE locale da Pacc                           **)
(**  ***************************************************************  **)

From Coq Require Import Bool.Bool.

From Loventre_Core Require Import Loventre_LMetrics.

From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Phase_Predicates
     Loventre_2SAT_Pacc_Class_Bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_2SAT_SAFE_Bridge.

  (** ------------------------------------------------------------ *)
  (** 1. Witness 2SAT                                              *)
  (** ------------------------------------------------------------ *)

  Parameter m_2sat_easy   : LMetrics.
  Parameter m_2sat_crit   : LMetrics.

  Hypothesis easy_is_pacc :
      is_pacc_2sat m_2sat_easy = true.

  Hypothesis crit_is_not_pacc :
      is_pacc_2sat m_2sat_crit = false.

  (** ------------------------------------------------------------ *)
  (** 2. SAFE e NON-SAFE definiti SOLO da Pacc                     *)
  (** ------------------------------------------------------------ *)

  (** Definizione locale: un input è SAFE se Pacc *)
  Definition SAFE_local (m : LMetrics) : Prop :=
    is_pacc_2sat m = true.

  (** Definizione locale di NON SAFE  *)
  Definition nonSAFE_local (m : LMetrics) : Prop :=
    is_pacc_2sat m = false.

  (** ------------------------------------------------------------ *)
  (** 3. Lemmi di appartenenza                                     *)
  (** ------------------------------------------------------------ *)

  Lemma easy_is_SAFE_local :
      SAFE_local m_2sat_easy.
  Proof.
    unfold SAFE_local.
    rewrite easy_is_pacc.
    reflexivity.
  Qed.

  Lemma crit_is_nonSAFE_local :
      nonSAFE_local m_2sat_crit.
  Proof.
    unfold nonSAFE_local.
    rewrite crit_is_not_pacc.
    reflexivity.
  Qed.

  (** ------------------------------------------------------------ *)
  (** 4. Teorema locale SAFE vs nonSAFE                            *)
  (** ------------------------------------------------------------ *)

  Theorem local_safe_split_2sat :
      SAFE_local m_2sat_easy
   /\ nonSAFE_local m_2sat_crit.
  Proof.
    split.
    - apply easy_isSAFE_local.
    - apply crit_is_nonSAFE_local.
  Qed.

End Loventre_2SAT_SAFE_Bridge.

