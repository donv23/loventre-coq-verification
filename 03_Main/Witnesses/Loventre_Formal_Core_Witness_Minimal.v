(*
  Minimal witness for the Loventre Formal Core
  Finite toy instantiation
*)

From Stdlib Require Import List.
Import ListNotations.

From Loventre_Advanced.Geometry Require Import Loventre_Formal_Core.

(* ====================================== *)
(* Concrete computational space           *)
(* ====================================== *)

Inductive Cw : Type :=
| c0 | c1 | c2.

Inductive Valw : Type :=
| v0 | v1.

Definition leValw (x y : Valw) : Prop :=
  match x, y with
  | v0, _ => True
  | v1, v1 => True
  | v1, v0 => False
  end.

Definition Rw (c d : Cw) : Prop :=
  match c, d with
  | c0, c1 => True
  | c1, c2 => True
  | _, _ => False
  end.

Definition kappaw (_ : Cw) : Valw := v0.
Definition entropyw (_ : Cw) : Valw := v0.
Definition compactnessw (_ : Cw) : Valw := v0.

Definition deltaw (_ : Cw -> Valw) (_ _ : Cw) : Valw := v0.

(* Deliberately trivial: no trajectory is efficient *)
Definition efficientw (_ : list Cw) : Prop := False.

Definition Targetw (c : Cw) : Prop := c = c2.

(* ====================================== *)
(* Local horizon definition               *)
(* ====================================== *)

Definition Horizonw (c : Cw) : Prop :=
  forall traj : list Cw,
    In c traj ->
    (exists cT, In cT traj /\ Targetw cT) ->
    ~ efficientw traj.

(* ====================================== *)
(* Concrete horizon example               *)
(* ====================================== *)

Lemma horizon_at_c0 : Horizonw c0.
Proof.
  unfold Horizonw, efficientw.
  intros traj _ _.
  intro H.
  exact H.
Qed.

