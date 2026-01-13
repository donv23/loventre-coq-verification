(** Loventre_Main_Classes.v
    Classi elementari basate su horizon_flag
    Gennaio 2026 — CANON BASE
 *)

From Stdlib Require Import Bool Reals.
From Loventre_Advanced Require Import Loventre_LMetrics_Core.
From Loventre_Main Require Import Loventre_Main_Witness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** ===========================
     Classificazione dei seed
    =========================== *)

Definition In_P_like (m : LMetrics) : Prop :=
  SAFE m.

Definition In_NP_blackhole_like (m : LMetrics) : Prop :=
  BlackHole m.

(** ===========================
       Lemmi di base
    =========================== *)

Lemma minimal_is_P :
  In_P_like m_seed_minimal.
Proof.
  unfold In_P_like, SAFE.
  reflexivity.
Qed.

Lemma critico_is_NP :
  In_NP_blackhole_like m_seed_critico.
Proof.
  unfold In_NP_blackhole_like, BlackHole.
  reflexivity.
Qed.

Close Scope R_scope.

