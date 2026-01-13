(** Loventre_Class_Properties.v
    Proprietà strutturali delle classi Loventre.
    V73 — SAFE -> Pacc con assioma locale di stabilità
 *)

From Stdlib Require Import Arith ZArith Lia.
From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types.
From Loventre_Advanced Require Import
  Loventre_SAFE_Model
  Loventre_Class_Model.

Import Loventre_Geometry.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z_scope.

(** ============================================================= *)
(** ASSIOMA LOCALE: un punto SAFE è stabilmente "calmo"            *)
(** ============================================================= *)

Axiom safe_implies_stable :
  forall x : M, is_safe x -> stable x.

(** ============================================================= *)
(** Pacc è contenuto in P                                          *)
(** ============================================================= *)

Lemma Pacc_implies_P :
  forall x : M,
    In_Pacc_Lov x ->
    In_P_Lov x.
Proof.
  unfold In_Pacc_Lov, In_P_Lov. tauto.
Qed.

(** ============================================================= *)
(** P e NPbh sono esclusivi                                        *)
(** ============================================================= *)

Lemma P_exclusive_NPbh :
  forall x : M,
    In_P_Lov x ->
    ~ In_NPbh_Lov x.
Proof.
  intros x HP HNP.
  apply In_NPbh_Lov_not_P in HNP.
  contradiction.
Qed.

(** ============================================================= *)
(** SAFE implica Pacc                                              *)
(** ============================================================= *)

Lemma SAFE_implies_Pacc :
  forall x : M,
    is_safe x ->
    In_Pacc_Lov x.
Proof.
  intros x HS.
  unfold In_Pacc_Lov, In_P_Lov.
  split.
  - (** SAFE implica contrattibile — placeholder semantico *)
    admit.
  - (** SAFE implica stabilità — via assioma locale *)
    apply safe_implies_stable; assumption.
Admitted.

