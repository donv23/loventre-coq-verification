(** Loventre_Main_2SAT_Classes.v
    Prima validazione della famiglia 2-SAT
    Versione V58-02 — Gennaio 2026
 *)

From Stdlib Require Import Bool.
From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Predicates
  Loventre_Main_Classes
  Loventre_Main_Witness_2SAT.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ===========================
      Lemmi base su 2-SAT
    =========================== *)

Lemma m_2SAT_easy_is_P_like :
  In_P_like m_2SAT_easy_demo.
Proof.
  unfold In_P_like, SAFE; simpl; reflexivity.
Qed.

Lemma m_2SAT_crit_is_blackhole :
  In_NP_blackhole_like m_2SAT_crit_demo.
Proof.
  unfold In_NP_blackhole_like, BlackHole; simpl; reflexivity.
Qed.

