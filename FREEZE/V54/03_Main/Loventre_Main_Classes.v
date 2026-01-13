(** Loventre_Main_Classes.v
    Definizione delle classi interne del modello Loventre
    Versione V54 — GENNAIO 2026
 *)

From Stdlib Require Import Reals Bool.

From Loventre_Advanced Require Import Loventre_LMetrics_Core.
From Loventre_Main Require Import Loventre_Main_Witness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** ===========================
      Classi interne del modello
    =========================== *)

(** Classe P_like: SAFE puro *)
Definition In_P_like (m : LMetrics) : Prop :=
  SAFE m.

(** Classe NP_blackhole_like: black hole puro *)
Definition In_NP_blackhole_like (m : LMetrics) : Prop :=
  BlackHole m.

(** Classe intermedia P_accessible_like:
    SAFE + asse indipendente su V0 (barriera) *)
Definition In_P_accessible_like (m : LMetrics) : Prop :=
  SAFE m /\ 0 <= V0 m.

(** ===========================
      Lemmi banali (coerenza)
    =========================== *)

Lemma P_like_implies_not_BH :
  forall m, In_P_like m -> ~ In_NP_blackhole_like m.
Proof.
  intros m Hsafe Hbh.
  unfold In_P_like, In_NP_blackhole_like in *.
  unfold SAFE, BlackHole in *.
  rewrite Hsafe in Hbh.
  discriminate.
Qed.

Lemma In_P_accessible_implies_P_like :
  forall m, In_P_accessible_like m -> In_P_like m.
Proof.
  intros m [Hsafe _].
  unfold In_P_like.
  exact Hsafe.
Qed.

Lemma In_NP_blackhole_like_not_safe :
  forall m, In_NP_blackhole_like m -> ~ In_P_like m.
Proof.
  intros m Hbh Hs.
  unfold In_P_like, In_NP_blackhole_like in *.
  unfold SAFE, BlackHole in *.
  rewrite Hbh in Hs.
  discriminate.
Qed.

Close Scope R_scope.

