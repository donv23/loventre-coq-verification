(**  ***************************************************************  **)
(**      Loventre Project — Geometry Layer — V85 Mini Theorem        **)
(**      CANON FILE — NO ASSIOMS — NO 03_Main                        **)
(**      Autore: Vincenzo Loventre + ChatGPT                         **)
(**      Stato: V85.2 — Mini Teorema Locale 2-SAT                    **)
(**  ***************************************************************  **)

From Coq Require Import Bool.Bool.

From Loventre_Core Require Import Loventre_LMetrics.

From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Phase_Predicates
     Loventre_2SAT_Pacc_Monotonicity
     Loventre_2SAT_Pacc_Lemma
     Loventre_2SAT_Phase_Separation
     Loventre_2SAT_Pacc_Class_Bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_2SAT_Mini_Theorem.

  (** ------------------------------------------------------------ *)
  (** 1. Witness — presi da fase e classe locale                   *)
  (** ------------------------------------------------------------ *)

  Parameter m_2sat_easy   : LMetrics.
  Parameter m_2sat_crit   : LMetrics.

  Hypothesis easy_is_pacc :
      is_pacc_2sat m_2sat_easy = true.

  Hypothesis crit_is_not_pacc :
      is_pacc_2sat m_2sat_crit = false.

  (** ------------------------------------------------------------ *)
  (** 2. Richiami di classe locale                                 *)
  (** ------------------------------------------------------------ *)

  Definition in_Pacc := fun m => is_pacc_2sat m = true.
  Definition in_NPbh := fun m => is_pacc_2sat m = false.

  Lemma easy_in_Pacc_local :
      in_Pacc m_2sat_easy.
  Proof.
    unfold in_Pacc; rewrite easy_is_pacc; reflexivity.
  Qed.

  Lemma crit_not_in_Pacc_local :
      in_NPbh m_2sat_crit.
  Proof.
    unfold in_NPbh; rewrite crit_is_not_pacc; reflexivity.
  Qed.

  (** ------------------------------------------------------------ *)
  (** 3. Mini Teorema Locale                                       *)
  (** ------------------------------------------------------------ *)
  (** Esistono witness espliciti, computati e verificati,
      con proprietà divergenti rispetto a Pacc.                    *)

  Theorem 2sat_pacc_mini_theorem :
      exists me mc,
         in_Pacc me
      /\ in_NPbh mc.
  Proof.
    exists m_2sat_easy, m_2sat_crit.
    split.
    - apply easy_in_Pacc_local.
    - apply crit_not_in_Pacc_local.
  Qed.

End Loventre_2SAT_Mini_Theorem.

