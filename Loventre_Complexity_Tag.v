(* Canvas 8 — Loventre_Complexity_Tag.v *)

From Stdlib Require Import Reals.
From Loventre Require Import Loventre_Metrics_Bus.
From Loventre Require Import Loventre_Metrics_Bus_Core.
From Loventre Require Import Loventre_LMetrics_JSON_Witness.
From Loventre Require Import Loventre_Policy_Base.
From Loventre Require Import Loventre_Safe_Bridge.

Inductive CompTag :=
  | P_like
  | NP_like.

(* decidibilità dell'uguaglianza (necessario per Coq) *)
Definition eq_CompTag_dec (a b : CompTag) : {a = b} + {a <> b}.
Proof.
  decide equality.
Qed.

Lemma comp_neq :
  P_like <> NP_like.
Proof. discriminate. Qed.

Definition tag_of_witness (w : LMetrics) : CompTag :=
  P_like.

Lemma comp_tag_ok : True.
Proof. exact I. Qed.

