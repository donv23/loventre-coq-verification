(** ============================================================= *)
(**                                                               *)
(**   Loventre_Proto_Witness.v                                   *)
(**   Canvas 14 — Fase 2 Kernel                                   *)
(**   Dicembre 2025                                               *)
(**                                                               *)
(** ============================================================= *)

From Stdlib Require Import Arith.

Require Import Loventre_Proto_Theorem.

Section Witness_Families.

  Variable Witness : Type.

  Variable is_P_like   : Witness -> Prop.
  Variable is_NP_like  : Witness -> Prop.

  Variable PWitness : nat -> Witness.
  Variable NPWitness : nat -> Witness.

  Hypothesis H_P_like_family :
    forall n, is_P_like (PWitness n).

  Hypothesis H_NP_like_family :
    forall n, is_NP_like (NPWitness n).

  (**
     Ogni n genera un witness P_like
  *)
  Lemma infinite_P_like :
    forall (n : nat), exists W, is_P_like W.
  Proof.
    intro n.
    assert (Hp : is_P_like (PWitness n)) by (apply (H_P_like_family n)).
    exists (PWitness n).
    exact Hp.
  Qed.

  (**
     Ogni n genera un witness NP_like
  *)
  Lemma infinite_NP_like :
    forall (n : nat), exists W, is_NP_like W.
  Proof.
    intro n.
    assert (Hnp : is_NP_like (NPWitness n)) by (apply (H_NP_like_family n)).
    exists (NPWitness n).
    exact Hnp.
  Qed.

  (**
     Versioni strutturali "airtight"
  *)
  Lemma stability_left :
    forall (n : nat), exists Wp, is_P_like Wp.
  Proof.
    intro n.
    destruct (infinite_P_like n) as [Wp Hp].
    exists Wp. exact Hp.
  Qed.

  Lemma stability_right :
    forall (n : nat), exists Wnp, is_NP_like Wnp.
  Proof.
    intro n.
    destruct (infinite_NP_like n) as [Wnp Hnp].
    exists Wnp. exact Hnp.
  Qed.

  (**
     TEOREMA STRUTTURALE — FORMA SICURA
  *)
  Theorem structural_stability :
    (forall (n : nat), exists Wp, is_P_like Wp) /\
    (forall (n : nat), exists Wnp, is_NP_like Wnp).
  Proof.
    split.
    - exact stability_left.
    - exact stability_right.
  Qed.

End Witness_Families.

(** ============================================================
    FINE CANVAS 14
    ============================================================ **)

