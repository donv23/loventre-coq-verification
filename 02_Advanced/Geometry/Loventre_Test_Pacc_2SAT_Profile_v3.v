(** Loventre_Test_Pacc_2SAT_Profile_v3.v
    Gennaio 2026 — V84.2.11
    Test minimale per P_accessible su 2-SAT
 *)

From Stdlib Require Import Reals Bool Lia Psatz.

From Loventre_Core Require Import Loventre_Kernel.
From Loventre_Advanced Require Import Loventre_LMetrics_Core.
From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_2SAT_LMetrics_From_JSON
  Loventre_2SAT_LMetrics_Crit_JSON
  Loventre_2SAT_EasyCrit_Compare.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** m_easy and m_crit are imported from their JSON providers *)

Definition is_Pacc_candidate (m : LMetrics) : Prop :=
  Rle (kappa_eff m) (kappa_eff m_crit).

Lemma easy_is_Pacc :
  is_Pacc_candidate m_easy.
Proof.
  unfold is_Pacc_candidate.
  unfold m_easy, m_crit.
  simpl; lra.
Qed.

Close Scope R_scope.

