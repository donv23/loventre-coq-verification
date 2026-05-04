Require Import Loventre_Advanced.LAB_A_Independence.A1_NoIrreversibility.Core_NoIrreversibility.

Inductive Cfg : Type := a | b.

Definition transM (_ _ : Cfg) : Prop := True.
Definition BarrierM (x : Cfg) : Prop := x = b.

Lemma barrier_exists : exists x, BarrierM x.
Proof. exists b; reflexivity. Qed.

Lemma global_reversibility :
  forall x y, transM x y -> transM y x.
Proof. intros; exact I. Qed.

