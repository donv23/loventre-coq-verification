(** Loventre_Risk_Level.v
    Classificazione logica del rischio nel modello Loventre.
    LIVELLO: Advanced — CANON (costruttivo, no logica classica)
*)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Params.

From Loventre_Advanced Require Import
  Loventre_Tunneling_Model
  Loventre_Barrier_Model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(** ============================================================= *)
(** Livelli astratti di rischio                                   *)
(** ============================================================= *)

Inductive Risk_Level : Set :=
| RISK_LOW
| RISK_MEDIUM
| RISK_HIGH.

(** ============================================================= *)
(** Predicati logici di classificazione                            *)
(** ============================================================= *)

Definition risk_low (x : M) : Prop :=
  ~ eventual_tunneling x.

Definition risk_medium (x : M) : Prop :=
  eventual_tunneling x.

Definition risk_high (x : M) : Prop :=
  exists n : nat, over_barrier (Flow n x).

(** ============================================================= *)
(** Osservazioni strutturali (CANON)                               *)
(** ============================================================= *)

(** NOTA CANON:
    - risk_high NON implica risk_medium
    - superare la barriera non garantisce tunneling
    - le classi NON sono ordinate per inclusione
*)

