(** Loventre_Main_Theorem.v
    Pre-separazione tripartita V54 — GENNAIO 2026
 *)

From Stdlib Require Import Reals Bool.
From Stdlib Require Import Lra.

From Loventre_Advanced Require Import Loventre_LMetrics_Core.
From Loventre_Main Require Import Loventre_Main_Witness Loventre_Main_Classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** ===========================
      Lemmi di appartenenza
    =========================== *)

Lemma minimal_is_P_like :
  In_P_like m_seed_minimal.
Proof.
  unfold In_P_like, SAFE, m_seed_minimal; simpl; reflexivity.
Qed.

Lemma middle_is_P_accessible :
  In_P_accessible_like m_seed_middle.
Proof.
  unfold In_P_accessible_like, SAFE, m_seed_middle; simpl.
  split.
  - reflexivity.
  - lra.
Qed.

Lemma critico_is_NP_blackhole :
  In_NP_blackhole_like m_seed_critico.
Proof.
  unfold In_NP_blackhole_like, BlackHole, m_seed_critico; simpl; reflexivity.
Qed.

(** ===========================
      Risultato di separazione
    =========================== *)

Theorem three_way_separation :
  exists m1, In_P_like m1 /\
  exists m2, In_P_accessible_like m2 /\
  exists m3, In_NP_blackhole_like m3.
Proof.
  exists m_seed_minimal. split.
  - exact minimal_is_P_like.
  - exists m_seed_middle. split.
    + exact middle_is_P_accessible.
    + exists m_seed_critico. exact critico_is_NP_blackhole.
Qed.

Close Scope R_scope.

