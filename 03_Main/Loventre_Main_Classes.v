(** Loventre_Main_Classes.v
    Classi principali (V57) — SAFE/P_ACC/BH unificate
 *)

From Stdlib Require Import Bool.

From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Predicates
  Loventre_Main_Witness.

From Loventre_Advanced Require Export
  Loventre_LMetrics_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================
      Classi nel modello Loventre
    ============================ *)

(** P-like = completamente SAFE *)
Definition In_P_like (m : LMetrics) : Prop :=
  SAFE m.

(** P-accessible = SAFE ma non collassa *)
Definition In_P_accessible_like (m : LMetrics) : Prop :=
  SAFE m /\ ~ BlackHole m.

(** NP-blackhole = collasso certo *)
Definition In_NP_blackhole_like (m : LMetrics) : Prop :=
  BlackHole m.

(** ============================
      Lemmi utili per Theorem
    ============================ *)

Lemma In_P_accessible_implies_P_like :
  forall m, In_P_accessible_like m -> In_P_like m.
Proof.
  intros m H.
  unfold In_P_accessible_like, In_P_like in *.
  exact (proj1 H).
Qed.

Lemma In_P_like_not_blackhole :
  forall m, In_P_like m -> ~ In_NP_blackhole_like m.
Proof.
  intros m Hp Hbh.
  unfold In_P_like, In_NP_blackhole_like, SAFE, BlackHole in *.
  rewrite Hp in Hbh.
  discriminate.
Qed.

