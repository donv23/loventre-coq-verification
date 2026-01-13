(** Loventre_Foundation_History_Structure.v
    Struttura di base per History nel modello Loventre. *)

From Stdlib Require Import List Arith Lia.

From Loventre_Core Require Import
  Loventre_Foundation_Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

Definition History := FiniteHistory.

(** Operazioni di base su History *)

Definition history_prefix (h1 h : History) : Prop :=
  exists h2 : History, h = h1 ++ h2.

Definition history_suffix (h2 h : History) : Prop :=
  exists h1 : History, h = h1 ++ h2.

Definition history_concat (h1 h2 : History) : History :=
  h1 ++ h2.

Definition history_segment (h : History) (i len : nat) : History :=
  firstn len (skipn i h).

(** Lemmi elementari sulle lunghezze *)

Lemma history_prefix_refl :
  forall h : History, history_prefix h h.
Proof.
  intros h.
  unfold history_prefix.
  exists (@nil _).
  now rewrite app_nil_r.
Qed.

Lemma history_suffix_refl :
  forall h : History, history_suffix h h.
Proof.
  intros h.
  unfold history_suffix.
  exists (@nil _).
  now rewrite app_nil_l.
Qed.

Lemma history_prefix_length_le :
  forall h1 h : History,
    history_prefix h1 h ->
    length h1 <= length h.
Proof.
  intros h1 h [h2 Hh].
  subst h.
  rewrite length_app.
  lia.
Qed.

Lemma history_suffix_length_le :
  forall h2 h : History,
    history_suffix h2 h ->
    length h2 <= length h.
Proof.
  intros h2 h [h1 Hh].
  subst h.
  rewrite length_app.
  lia.
Qed.

Lemma history_concat_length :
  forall h1 h2 : History,
    length (history_concat h1 h2) = length h1 + length h2.
Proof.
  intros h1 h2.
  unfold history_concat.
  apply length_app.
Qed.

