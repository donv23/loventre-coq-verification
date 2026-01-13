(** Loventre_2SAT_EasyCrit_Compare.v
    Confronto tra profili easy e critici 2SAT
    Gennaio 2026 — V84.2.10
 *)

From Stdlib Require Import Reals Bool.
From Stdlib Require Import Reals.RIneq Reals.Ranalysis Reals.Raxioms.
From Stdlib Require Import Psatz.

From Loventre_Core Require Import Loventre_Kernel.
From Loventre_Advanced Require Import Loventre_LMetrics_Core.
From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_2SAT_LMetrics_From_JSON
  Loventre_2SAT_LMetrics_Crit_JSON.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** ====================================================== *)
(**    Confronto diagnostico fra profili easy e critici    *)
(** ====================================================== *)

Definition easy_less_than_crit (e c : LMetrics) : Prop :=
  (kappa_eff e <= kappa_eff c)%R /\
  (entropy_eff e <= entropy_eff c)%R /\
  (V0 e <= V0 c)%R.

Lemma easy_vs_crit_true :
  easy_less_than_crit m_easy m_crit.
Proof.
  unfold easy_less_than_crit, m_easy, m_crit.
  simpl; split; try lra; split; lra.
Qed.

Close Scope R_scope.

