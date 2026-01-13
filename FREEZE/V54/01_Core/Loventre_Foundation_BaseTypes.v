(** Loventre_Foundation_BaseTypes.v
    Tipi di base richiesti per History, Time e Regimes. *)

From Stdlib Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

(** Indice temporale di base *)
Definition TimeIndex := nat.

(** Una History finita è una lista di TimeIndex
    (placeholder fino a estensioni successive) *)
Definition FiniteHistory := list TimeIndex.

