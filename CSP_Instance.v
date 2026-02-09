(* ======================================================= *)
(* CSP_Instance.v                                         *)
(* S3 — Istanziazione concreta minimale (stabile)         *)
(* ======================================================= *)

From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------- *)
(* Oggetto e configurazioni                                *)
(* ------------------------------------------------------- *)

Inductive Obj : Type :=
| CSP : Obj.

Definition Config (X : Obj) : Type :=
  nat -> nat.

(* ------------------------------------------------------- *)
(* Struttura locale (ignorata)                             *)
(* ------------------------------------------------------- *)

Inductive FiniteSub (X : Obj) : Type :=
| dummy : FiniteSub X.

Definition Restrict {X : Obj} (c : Config X) (F : FiniteSub X) : unit :=
  tt.

(* ------------------------------------------------------- *)
(* Order Property locale                                   *)
(* ------------------------------------------------------- *)

Definition OP_local (X : Obj) : Prop :=
  exists (C : nat -> Config X),
    (forall (F : FiniteSub X) (i j : nat),
        Restrict (C i) F = Restrict (C j) F)
    /\
    (forall (i j : nat), i <> j -> C i <> C j).

(* ------------------------------------------------------- *)
(* Famiglia di configurazioni                              *)
(* ------------------------------------------------------- *)

Definition C (i : nat) : Config CSP :=
  fun _ => i.

Lemma C_local_indist :
  forall (F : FiniteSub CSP) (i j : nat),
    Restrict (C i) F = Restrict (C j) F.
Proof.
  intros; reflexivity.
Qed.

(* Assioma locale: distinzione globale *)
Axiom C_global_distinct :
  forall (i j : nat), i <> j -> C i <> C j.

(* ------------------------------------------------------- *)
(* OP_local vale per CSP                                   *)
(* ------------------------------------------------------- *)

Theorem CSP_has_OP_local :
  OP_local CSP.
Proof.
  unfold OP_local.
  exists C.
  split.
  - apply C_local_indist.
  - apply C_global_distinct.
Qed.

