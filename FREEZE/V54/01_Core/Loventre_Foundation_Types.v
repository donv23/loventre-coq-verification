(** Loventre_Foundation_Types.v
    Tipi di base del modello Loventre.
 *)

From Stdlib Require Import List Arith Lia.

(* Nessun import Loventre ancora: questo file è il basamento *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.

(** === Tipi primitivi Loventre === *)

(* Indici temporali *)
Definition TimeIndex := nat.

(* Storia come lista di eventi (per ora nat placeholder) *)
Definition HistoryEvent := nat.
Definition FiniteHistory := list HistoryEvent.

(* Valori generici per parametri *)
Definition LoventreReal := nat.     (* placeholder per ora *)
Definition LoventreInt  := nat.

(** === Alias semantici di comodo === *)

Definition LValue := LoventreReal.
Definition LIndex := nat.

(** === Derivati principali === *)

Definition CurveValue := LoventreReal.
Definition EntropyValue := LoventreReal.
Definition MassValue := LoventreReal.
Definition PotentialValue := LoventreReal.

(** === Contenitore base per i parametri === *)

Record BaseConfig := {
  cfg_mass : MassValue;
  cfg_entropy : EntropyValue
}.

