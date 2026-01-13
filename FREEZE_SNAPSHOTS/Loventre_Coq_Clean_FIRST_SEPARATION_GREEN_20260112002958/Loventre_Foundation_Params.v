(** Loventre_Foundation_Params.v
    Parametri fondamentali del modello Loventre.
    CANON — dicembre 2025 *)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z_scope.

Import Loventre_Geometry.

(** ============================================================= *)
(** Parametri globali canonici del modello Loventre                *)
(** ============================================================= *)

(** Coefficienti del potenziale *)
Parameter alpha_L : Z.
Parameter beta_L  : Z.

(** Spessore minimo discreto della barriera *)
Parameter a_min_L : nat.

