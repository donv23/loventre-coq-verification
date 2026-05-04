(*
  CounterModel_Basin.v
  LAB-A3: Barriers are traversable; no terminal confinement forced.
*)

Require Import Loventre_Advanced.LAB_A_Independence.A3_NoTerminality.Core_NoTerminality.

Inductive Cfg : Type := u | v.

Definition transM (_ _ : Cfg) : Prop := True.
Definition BarrierM (x : Cfg) : Prop := x = v.

Lemma barrier_not_terminal :
  exists x y z : Cfg, transM x y /\ BarrierM y /\ transM y z.
Proof.
  exists u, v, u; repeat split; try reflexivity; exact I.
Qed.

