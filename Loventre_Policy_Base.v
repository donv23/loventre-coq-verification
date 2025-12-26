(* Tab 2 — Canvas 1 — Loventre_Policy_Base.v *)

From Stdlib Require Import Reals.
From Loventre Require Import Loventre_Metrics_Bus.
From Loventre Require Import Loventre_LMetrics_JSON_Witness.

Inductive SafeState :=
  | SAFE
  | UNSAFE.

Lemma safe_neq_unsafe : SAFE <> UNSAFE.
Proof. discriminate. Qed.

Definition policy_of_witness (w : LMetrics) : SafeState :=
  SAFE.

Lemma policy_base_ok : True.
Proof. exact I. Qed.

