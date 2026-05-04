(*
  Loventre_Core_Prelude.v

  Core canonico minimale del progetto Loventre.
  Questo file NON dipende da Advanced né da Geometry.

  Ruolo:
  - fissare gli import Stdlib
  - fornire un punto di aggancio stabile per tutto il progetto
  - evitare dipendenze cicliche o path ambigui

  Dicembre 2025 — CANON
*)

From Stdlib Require Import
  Reals
  Lists.List
  Bool.Bool
  Arith.Arith
  Logic.Classical_Prop.

Import ListNotations.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------------- *)
(* Convenzioni globali Loventre                                                *)
(* -------------------------------------------------------------------------- *)

(* Alias semantici di base — il Core NON conosce Geometry *)
Definition Real := R.
Definition Nat  := nat.
Definition Bool := bool.

(* -------------------------------------------------------------------------- *)
(* Fine Core Prelude                                                           *)
(* -------------------------------------------------------------------------- *)

