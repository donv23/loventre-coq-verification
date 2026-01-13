(** Loventre_Main_Theorem_V58.v
    Mini-Teorema Esteso (due famiglie)
    Versione V58-03 — Gennaio 2026
 *)

From Stdlib Require Import Bool.

From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Witness
  Loventre_Main_Witness_2SAT
  Loventre_Main_Predicates
  Loventre_Main_Classes
  Loventre_Main_2SAT_Classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================
      MINI TEOREMA ESTESO V58
    ============================ *)

Theorem loventre_internal_multi_family_separation_v58 :
  In_P_like m_seed_minimal /\
  In_P_accessible_like m_seed_middle /\
  In_NP_blackhole_like m_seed_critico /\
  In_P_like m_2SAT_easy_demo /\
  In_NP_blackhole_like m_2SAT_crit_demo.
Proof.
  repeat split.
  - unfold In_P_like, SAFE; simpl; reflexivity.
  - unfold In_P_accessible_like, SAFE; simpl.
    split; [reflexivity|].
    unfold BlackHole; simpl; intro H; discriminate.
  - unfold In_NP_blackhole_like, BlackHole; simpl; reflexivity.
  - exact m_2SAT_easy_is_P_like.
  - exact m_2SAT_crit_is_blackhole.
Qed.

(** ============================
      COROLLARIO DI ESISTENZA
    ============================ *)

Corollary loventre_internal_multi_family_exists_v58 :
  exists m1 m2 m3 m4 m5,
       In_P_like m1
    /\ In_P_accessible_like m2
    /\ In_NP_blackhole_like m3
    /\ In_P_like m4
    /\ In_NP_blackhole_like m5.
Proof.
  exists m_seed_minimal,
         m_seed_middle,
         m_seed_critico,
         m_2SAT_easy_demo,
         m_2SAT_crit_demo.
  apply loventre_internal_multi_family_separation_v58.
Qed.

