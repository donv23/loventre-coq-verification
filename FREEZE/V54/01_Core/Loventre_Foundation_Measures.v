From Stdlib Require Import List Arith Lia.
Import ListNotations.

Local Open Scope nat_scope.

(** * Basic numeric measures on lists of nat *)

(** Sum of a list of natural numbers. *)

Fixpoint nat_sum (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => x + nat_sum xs
  end.

Lemma nat_sum_nil : nat_sum [] = 0.
Proof. reflexivity. Qed.

Lemma nat_sum_cons :
  forall x l, nat_sum (x :: l) = x + nat_sum l.
Proof. reflexivity. Qed.

Lemma nat_sum_app :
  forall l1 l2,
    nat_sum (l1 ++ l2) = nat_sum l1 + nat_sum l2.
Proof.
  induction l1 as [|x xs IH]; intros l2.
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

(** Maximum of a list of natural numbers.
    Convention: the max of the empty list is 0. *)

Fixpoint nat_max (l : list nat) : nat :=
  match l with
  | [] => 0
  | x :: xs => Nat.max x (nat_max xs)
  end.

Lemma nat_max_nil : nat_max [] = 0.
Proof. reflexivity. Qed.

Lemma nat_max_cons :
  forall x l, nat_max (x :: l) = Nat.max x (nat_max l).
Proof. reflexivity. Qed.

Lemma nat_max_le :
  forall l x, In x l -> x <= nat_max l.
Proof.
  induction l as [|y ys IH]; intros x HIn.
  - inversion HIn.
  - simpl in *. destruct HIn as [Hx | HIn'].
    + subst. apply Nat.le_max_l.
    + specialize (IH _ HIn'). eapply Nat.le_trans; [exact IH|].
      apply Nat.le_max_r.
Qed.

Lemma nat_max_ge_0 :
  forall l, 0 <= nat_max l.
Proof.
  intros l. induction l as [|x xs IH]; simpl; lia.
Qed.

(** Mean value of a list of natural numbers.
    Convention: mean of the empty list is 0. *)

Definition nat_mean_data (l : list nat) : nat :=
  match l with
  | [] => 0
  | _ => nat_sum l / length l
  end.

Lemma nat_mean_data_nil :
  nat_mean_data [] = 0.
Proof. reflexivity. Qed.

(** A simple quantile index on [0; length l - 1].
    We interpret [q] as a percentage in [0;100].
    Convention: on empty list we return 0. *)

Definition nat_quantile_index (q : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | _ =>
      let n := length l in
      Nat.min (n - 1) ((q * (n - 1)) / 100)
  end.

