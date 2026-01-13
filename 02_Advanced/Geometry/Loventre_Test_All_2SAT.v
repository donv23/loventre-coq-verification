(** Loventre_Test_All_2SAT.v
    Gennaio 2026 — V84.2.12
    Test consolidato su m_easy e m_crit
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

(** Proprietà diagnostiche elementari *)

Lemma easy_kappa_below_crit :
  kappa_eff m_easy <= kappa_eff m_crit.
Proof. simpl; lra. Qed.

Lemma crit_not_below_easy :
  kappa_eff m_crit >= kappa_eff m_easy.
Proof. simpl; lra. Qed.

Lemma entropy_easy_nonneg :
  0 <= entropy_eff m_easy.
Proof. simpl; lra. Qed.

Lemma entropy_crit_nonneg :
  0 <= entropy_eff m_crit.
Proof. simpl; lra. Qed.

Close Scope R_scope.

