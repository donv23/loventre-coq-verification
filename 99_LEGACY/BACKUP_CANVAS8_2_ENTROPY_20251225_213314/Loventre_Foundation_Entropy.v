(** Loventre_Foundation_Entropy.v
    Entropia lungo stati e history nel modello Loventre. *)

From Coq Require Import List Arith ZArith.

Require Import Loventre_Kernel.
Require Import Loventre_Foundation_Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Import Loventre_Geometry.

Parameter Entropy_L : State -> Z.

Definition entropy_at_time (x : State) (n : TimeIndex) : Z :=
  Entropy_L (Flow n x).

Definition entropy_history (h : FiniteHistory) : list Z :=
  map Entropy_L h.

Definition entropy_sum_history (h : FiniteHistory) : Z :=
  fold_left Z.add (entropy_history h) 0%Z.

Definition entropy_prefix (h : FiniteHistory) (n : nat) : list Z :=
  firstn n (entropy_history h).

Lemma entropy_history_length :
  forall h : FiniteHistory,
    length (entropy_history h) = length h.
Proof.
  intro h.
  unfold entropy_history.
  now rewrite map_length.
Qed.

