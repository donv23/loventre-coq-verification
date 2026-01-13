(** Loventre_Class_Model.v
    Definizione delle classi P-like, Pacc e NPbh nel modello Loventre.
    Rocq 9.1 — CANON composizionale
 *)

From Stdlib Require Import Arith ZArith Lia.
From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types.
From Loventre_Advanced Require Import
  Loventre_SAFE_Model.

Import Loventre_Geometry.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z_scope.

(** ========================================================== **)
(**  Tag discreto di classe, visibile ai witness JSON           **)
(** ========================================================== **)

Inductive Class_Tag : Type :=
| Class_P_str      (* P-like forte = contractibile *)
| Class_P_acc      (* P-accessibile = contractibile + stabile *)
| Class_NP_bh.     (* NP-like-black-hole = non contrattibile *)


(** ========================================================== **)
(**  Predicati semantici canonici                              **)
(** ========================================================== **)

Definition In_P_Lov (x : M) : Prop :=
  contractible x.

Definition In_Pacc_Lov (x : M) : Prop :=
  contractible x /\ stable x.

Definition In_NPbh_Lov (x : M) : Prop :=
  non_contractible x.

(** ========================================================== **)
(**  Lemmi di esclusione di base                               **)
(** ========================================================== **)

Lemma In_NPbh_Lov_not_P :
  forall x : M,
    In_NPbh_Lov x ->
    ~ In_P_Lov x.
Proof.
  unfold In_NPbh_Lov, In_P_Lov.
  intros x HNP HP.
  apply non_contractible_exclusive with (x:=x); assumption.
Qed.

(** ========================================================== **)
(**  Fine file CANON v2026-01-12                               **)
(** ========================================================== **)

