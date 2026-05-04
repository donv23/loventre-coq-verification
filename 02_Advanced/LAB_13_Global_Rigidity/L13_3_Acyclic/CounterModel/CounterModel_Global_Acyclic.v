(*
  LAB-13.3 — CounterModel_Global_Acyclic.v (v1 canonica, gennaio 2026)

  Contromodello: Acyclic (no self-loop) può valere,
  ma GlobalPathRigid può fallire (2-cycle a<->b).

  Questo nega: Acyclic -> GlobalPathRigid.
*)

Require Import
  Loventre_Advanced.LAB_13_Global_Rigidity.L13_3_Acyclic.Core.Core_Global_Acyclic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Configurazioni concrete === *)

Inductive Config : Type :=
| a
| b
| c.

(* === Relazione path (con 2-cycle a<->b, nessun self-loop) === *)

Inductive path : Config -> Config -> Prop :=
| p_ab : path a b
| p_ba : path b a
| p_bc : path b c.

(* === Lemmi base di disequazione === *)

Lemma a_neq_b : a <> b. Proof. discriminate. Qed.
Lemma b_neq_a : b <> a. Proof. discriminate. Qed.

(* === Acyclic (debole) vale: nessun path x x === *)

Lemma Acyclic_holds :
  Core_Global_Acyclic.Acyclic (Config:=Config) path.
Proof.
  unfold Core_Global_Acyclic.Acyclic.
  intros x Hxx.
  inversion Hxx.
Qed.

(* === GlobalPathRigid fallisce (per a<->b) === *)

Lemma not_GlobalPathRigid :
  ~ Core_Global_Acyclic.GlobalPathRigid (Config:=Config) path.
Proof.
  unfold Core_Global_Acyclic.GlobalPathRigid.
  intro H.
  specialize (H a b).
  assert (Core_Global_Acyclic.nontrivial_path (Config:=Config) path a b) as Hnt.
  { unfold Core_Global_Acyclic.nontrivial_path. split.
    - exact a_neq_b.
    - exact p_ab.
  }
  (* H dice: non può valere path b a, ma noi abbiamo p_ba *)
  exact (H Hnt p_ba).
Qed.

(* === Quindi: Acyclic non forza GlobalPathRigid === *)

Lemma not_Acyclic_Forces_GlobalPathRigid :
  ~ Core_Global_Acyclic.Acyclic_Forces_GlobalPathRigid (Config:=Config) path.
Proof.
  unfold Core_Global_Acyclic.Acyclic_Forces_GlobalPathRigid.
  intro H.
  apply not_GlobalPathRigid.
  apply H.
  exact Acyclic_holds.
Qed.
