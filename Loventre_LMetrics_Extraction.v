(** ============================================================= *)
(**   Loventre_LMetrics_Extraction.v                              *)
(**   Canvas 18 — Fase 2 Kernel                                   *)
(** ============================================================= *)

From Stdlib Require Import Arith.

Require Import Loventre_LMetrics_Kernel.
Require Import Loventre_LMetrics_Structural.

Section LMetrics_Extraction.

  Variable Witness : Type.

  Variable is_P_like   : Witness -> Prop.
  Variable is_NP_like  : Witness -> Prop.

  Variable reducible   : Witness -> Witness -> Prop.
  Variable equivalent  : Witness -> Witness -> Prop.

  Variable PWitness : nat -> Witness.
  Variable NPWitness : nat -> Witness.

  Hypothesis H_P_like_family :
    forall (n : nat), is_P_like (PWitness n).

  Hypothesis H_NP_like_family :
    forall (n : nat), is_NP_like (NPWitness n).

  Hypothesis H_irreducible :
    forall (Wp Wnp : Witness),
      is_P_like Wp ->
      is_NP_like Wnp ->
      ~ reducible Wnp Wp.

  Hypothesis H_equiv_implies_reducible :
    forall (Wp Wnp : Witness),
      equivalent Wnp Wp ->
      reducible Wnp Wp.

  Variable LProfile_of : Witness -> LMetrics.

  Hypothesis H_legal_profile :
    forall w, LM_legal (LProfile_of w).

  (**
     TEORIA FINALE LOCALE COSTRUTTIVA
     P-like != NP-like da un punto di vista equivalenziale
  *)
  Theorem LMetrics_global_separation :
    forall Wp Wnp,
      is_P_like Wp ->
      is_NP_like Wnp ->
      ~ equivalent Wnp Wp.
  Proof.
    intros Wp Wnp HP HNP Heq.

    (* 1: da equivalenza ⇒ riducibilità *)
    assert (Hred : reducible Wnp Wp).
    { apply H_equiv_implies_reducible. exact Heq. }

    (* 2: da P-like & NP-like ⇒ non riducibile *)
    assert (Hirr : ~ reducible Wnp Wp).
    { apply (H_irreducible Wp Wnp); assumption. }

    (* 3: contraddizione *)
    exact (Hirr Hred).
  Qed.

End LMetrics_Extraction.

