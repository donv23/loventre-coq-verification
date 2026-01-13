(** Loventre_SAFE_Model.v
    Predicato SAFE fondato sui livelli di rischio.
    Versione CANON v2026-01 — Rocq 9.1
*)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Params.

From Loventre_Advanced Require Import
  Loventre_Risk_Level.

Import Loventre_Geometry.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z_scope.

(** -------------------------------------------------------------------- *)
(** Definizione canonica di SAFE                                         *)
(** SAFE = nessun tunneling e nessun superamento barriera                *)
(** cioè rischio basso + NON rischio alto                                *)
(** -------------------------------------------------------------------- *)

Definition is_safe (x : M) : Prop :=
  risk_low x /\ ~ risk_high x.

(** Nota:
    - risk_low : ~ eventual_tunneling x
    - risk_high: exists n, over_barrier (Flow n x)
    Quindi SAFE significa evitare sia tunneling sia overshoot
*)

(** Proprietà di base — CANON minimale *)

Lemma SAFE_implies_risk_low :
  forall x : M, is_safe x -> risk_low x.
Proof.
  intros x H. exact (proj1 H).
Qed.

Lemma SAFE_excludes_risk_high :
  forall x : M, is_safe x -> ~ risk_high x.
Proof.
  intros x H. exact (proj2 H).
Qed.

