(*
  LAB-13.2 — CounterModel_Global_Path.v

  Contromodello che mostra:
  la rigidità globale basata su path
  NON è forzata dalle assunzioni del core.
*)

Require Import
  Loventre_Advanced.LAB_13_Global_Rigidity.L13_1_Core.Core_Global_Path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Configurazioni concrete === *)

Inductive C : Type :=
| a
| b.

Definition Config := C.

(* === Uguaglianza decidibile === *)

Lemma a_neq_b : a <> b.
Proof. discriminate. Qed.

Lemma b_neq_a : b <> a.
Proof. discriminate. Qed.

(* === Relazione di path concreta === *)

Inductive pathM : Config -> Config -> Prop :=
| pab : pathM a b
| pba : pathM b a.

Definition path := pathM.

(* === Proprietà di non-trivialità === *)

Definition nontrivial_path (x y : Config) : Prop :=
  x <> y /\ path x y.

(* === Fallimento della rigidità globale === *)

Lemma not_Global_Path_Rigid :
  ~ (forall x y : Config,
        nontrivial_path x y -> ~ path y x).
Proof.
  intro H.

  assert (Hab : nontrivial_path a b).
  { split; [exact a_neq_b | exact pab]. }

  specialize (H a b Hab).

  apply H.
  exact pba.
Qed.

