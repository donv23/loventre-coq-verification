(** Loventre_Foundation_Entropy.v
    Fondazioni entropiche del modello Loventre.
    CANON — dicembre 2025 *)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(** Entropia informazionale astratta *)

Parameter Entropy_L : M -> Z.


