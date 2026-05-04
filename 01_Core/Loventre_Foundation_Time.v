(** Loventre_Foundation_Time.v
    Strutture temporali di base per il modello Loventre. *)

From Coq Require Import List Arith Lia.

Require Import Loventre_Foundation_Types.
Require Import Loventre_Foundation_History_Structure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

(** Indice temporale di base *)

Definition Time := TimeIndex.

(** Intervalli di tempo *)

Record TimeInterval := {
  t_start : Time;
  t_end   : Time
}.

Definition time_interval_well_formed (I : TimeInterval) : Prop :=
  (t_start I <= t_end I)%nat.

Definition time_in_interval (n : Time) (I : TimeInterval) : Prop :=
  (t_start I <= n <= t_end I)%nat.

(** Relazione di prefisso su History *)

Definition is_history_prefix_of (h1 h2 : History) : Prop :=
  history_prefix h1 h2.

Lemma is_history_prefix_of_refl :
  forall h : History, is_history_prefix_of h h.
Proof.
  intro h.
  unfold is_history_prefix_of.
  apply history_prefix_refl.
Qed.

Lemma is_history_prefix_of_length_le :
  forall h1 h2 : History,
    is_history_prefix_of h1 h2 ->
    length h1 <= length h2.
Proof.
  intros h1 h2 Hpre.
  unfold is_history_prefix_of in Hpre.
  eapply history_prefix_length_le; eauto.
Qed.

Lemma is_history_prefix_of_trans :
  forall h1 h2 h3 : History,
    is_history_prefix_of h1 h2 ->
    is_history_prefix_of h2 h3 ->
    is_history_prefix_of h1 h3.
Proof.
  intros h1 h2 h3 H12 H23.
  unfold is_history_prefix_of, history_prefix in *.
  destruct H12 as [h12 H12].
  destruct H23 as [h23 H23].
  subst h2 h3.
  exists (h12 ++ h23).
  now rewrite app_assoc.
Qed.

