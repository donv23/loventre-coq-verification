(** Loventre_Foundation_Complexity.v
    Complessità lungo stati e history nel modello Loventre. *)

From Coq Require Import List Arith ZArith.

Require Import Loventre_Kernel.
Require Import Loventre_Foundation_Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Import Loventre_Geometry.

Definition Complexity_L (x : State) : nat :=
  Complexity x.

Definition complexity_at_time (x : State) (n : TimeIndex) : nat :=
  Complexity_L (Flow n x).

Definition complexity_history (h : FiniteHistory) : list nat :=
  map Complexity_L h.

Definition complexity_sum_history (h : FiniteHistory) : nat :=
  fold_left Nat.add (complexity_history h) 0%nat.

Definition complexity_prefix (h : FiniteHistory) (n : nat) : list nat :=
  firstn n (complexity_history h).

Lemma complexity_history_length :
  forall h : FiniteHistory,
    length (complexity_history h) = length h.
Proof.
  intro h.
  unfold complexity_history.
  now rewrite map_length.
Qed.

