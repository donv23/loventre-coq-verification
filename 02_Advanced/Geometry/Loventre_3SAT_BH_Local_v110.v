(* ========================================================================= *)
(*  Loventre_3SAT_BH_Local_v110.v                                            *)
(*  Modulo 3SAT – Black-Hole Local Gate (v110)                               *)
(*  Progetto Loventre – Gennaio 2026                                         *)
(*                                                                           *)
(*  Nessun assioma. Nessuna dipendenza da 03_Main.                           *)
(*  Estensione locale coerente con SAFE + CLASS già definiti in v105–107.   *)
(*                                                                           *)
(* ========================================================================= *)

From Loventre_Core     Require Import Loventre_Core_Prelude.
From Loventre_Core     Require Import Loventre_Foundation_Types.
From Loventre_Core     Require Import Loventre_Foundation_Params.
From Loventre_Core     Require Import Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import Loventre_LMetrics_Core.
From Loventre_Advanced Require Import Loventre_Metrics_Bus.
From Loventre_Advanced Require Import Loventre_SAFE_Model.
From Loventre_Advanced Require Import Loventre_Class_Model.

(*  3SAT support v104–107 *)
From Loventre_Advanced.Geometry
     Require Import
          Loventre_3SAT_Decode_Compute_v104
          Loventre_3SAT_SAFE_Local_v105
          Loventre_3SAT_Class_Local_v107.

(* ========================================================================= *)
(*  Black-Hole Local Predicate                                               *)
(* ========================================================================= *)

Definition is_3SAT_bh_local (m : LMetrics) : Prop :=
  (* BH locale è attivo quando:
     - classe non in_P_like locale
     - SAFE locale fallisce
     - rischio / chi / barriere indicano slittamento fuori controllo
     Questa è una versione minimal coerente:
  *)
  (in_3SAT_class_local m = in_beyond_p_local)
  /\ (is_3SAT_safe_local m = false)
  /\ (risk_index m > 5)%nat.

(* ========================================================================= *)
(*  Boundary Local Predicate                                                 *)
(* ========================================================================= *)

Definition is_3SAT_boundary_local (m : LMetrics) : Prop :=
  (* transizione tra SAFE e BH *)
  (is_3SAT_safe_local m = false)
  /\ (in_3SAT_class_local m = in_boundary_local).

(* ========================================================================= *)
(*  P-like Local Predicate                                                   *)
(* ========================================================================= *)

Definition is_3SAT_plike_local (m : LMetrics) : Prop :=
  (is_3SAT_safe_local m = true)
  /\ (in_3SAT_class_local m = in_p_like_local).

(* ========================================================================= *)
(*  Lemmi di coerenza MINIMALI                                              *)
(* ========================================================================= *)

Lemma plike_local_not_bh_local :
  forall m, is_3SAT_plike_local m -> ~ is_3SAT_bh_local m.
Proof.
  intros m [Hsafe Hclass] [Hbclass [Hbsafe _]].
  unfold is_3SAT_safe_local in *.
  congruence.
Qed.

Lemma bh_local_not_plike_local :
  forall m, is_3SAT_bh_local m -> ~ is_3SAT_plike_local m.
Proof.
  intros m [Hclass [Hsafe _]] [Hpsafe _].
  unfold is_3SAT_safe_local in *.
  congruence.
Qed.

Lemma plike_or_boundary_or_bh_local :
  forall m,
    is_3SAT_plike_local m
    \/ is_3SAT_boundary_local m
    \/ is_3SAT_bh_local m.
Proof.
  intros m.
  unfold is_3SAT_plike_local, is_3SAT_boundary_local, is_3SAT_bh_local.
  destruct (is_3SAT_safe_local m) eqn:Hsafe.
  - destruct (in_3SAT_class_local m); try now left; try now left.
  - destruct (in_3SAT_class_local m).
    + right; right; split; auto; split; auto; lia.
    + right; left; split; auto.
    + right; right; split; auto; split; auto; lia.
Qed.

(* ========================================================================= *)
(*  Fine file v110 – nessun assioma                                          *)
(* ========================================================================= *)

