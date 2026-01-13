(*
  Loventre_TimeChain_V810.v
  Versione: V810 (Canvas 2 — Dinamica Informazionale)
  Obiettivo:
    - costruire evoluzione discreta a passi multipli su LMetrics
    - collegare evolve_once (V800) a evolve_n
    - introdurre semigruppo discreto su nat
  Stato: CANON — nessun assioma, nessun JSON, nessun witness incorporato
*)

From Coq Require Import Reals.
From Coq Require Import Lia.

From Loventre_Core Require Import Loventre_Prelude.
From Loventre_Core Require Import Loventre_LMetrics_Core.
From Loventre_Advanced Require Import Loventre_Phase_Predicates.
From Loventre_Advanced Require Import Loventre_TimeEvolution_V800.

Open Scope R_scope.

Module Loventre_TimeChain_V810.

  (**
     EVOLVE_N: applica evolve_once n volte
     Definizione naturale su nat
  *)

  Fixpoint evolve_n (n : nat) (m : LMetrics) : LMetrics :=
    match n with
    | O => m
    | S k => evolve_once (evolve_n k m)
    end.

  (**
     IDENTITÀ BASE
     evolve_n 0 = identità
     evolve_n 1 = evolve_once
     evolve_n 2 = evolve_twice
  *)
  Lemma evolve_n_zero :
    forall m, evolve_n 0 m = m.
  Proof. reflexivity. Qed.

  Lemma evolve_n_one :
    forall m, evolve_n 1 m = evolve_once m.
  Proof. reflexivity. Qed.

  Lemma evolve_n_two :
    forall m, evolve_n 2 m = evolve_twice m.
  Proof. reflexivity. Qed.

  (**
     COMPOSIZIONE DISCRETA
     evolve_n (n+m) = evolve_n n ∘ evolve_n m
     (primo tassello del semigruppo su nat)
     Nota: dimostrazione per induzione su n
  *)

  Lemma evolve_n_semigroup :
    forall n m (x : LMetrics),
      evolve_n (n + m) x = evolve_n n (evolve_n m x).
  Proof.
    intros n m x; induction n as [|n IH].
    - simpl; reflexivity.
    - simpl. rewrite IH. reflexivity.
  Qed.

  (**
     MONOTONIA SU p_tunnel
     dedotta da monotonia evolve_once
  *)
  Lemma evolve_n_increases_tunnel :
    forall n m,
      evolve_n n m.(p_tunnel) >= m.(p_tunnel).
  Proof.
    intros n m; induction n.
    - simpl; right; reflexivity.
    - simpl; unfold evolve_once; simpl.
      apply Rle_trans with (r2 := evolve_n n m.(p_tunnel)).
      + apply IHn.
      + apply Rle_min_l.
  Qed.

  (**
     COMMENTO TECNICO:
     V810 stabilisce:
       - identità
       - passo discreto
       - semigruppo su nat
       - monotonia fondamentale
     La no-return e irreversibilità compaiono in V820+
  *)

End Loventre_TimeChain_V810.

