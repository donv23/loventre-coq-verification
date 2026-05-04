(* Canvas 11 — Loventre_Complexity_Reduction.v *)

From Stdlib Require Import Reals.
Require Import Coq.micromega.Lra.

From Loventre Require Import Loventre_Metrics_Bus.
From Loventre Require Import Loventre_Metrics_Bus_Core.
From Loventre Require Import Loventre_LMetrics_JSON_Witness.
From Loventre Require Import Loventre_Policy_Base.
From Loventre Require Import Loventre_Safe_Bridge.
From Loventre Require Import Loventre_Complexity_Tag.
From Loventre Require Import Loventre_Complexity_Bridge.
From Loventre Require Import Loventre_Complexity_Separation.

Open Scope R_scope.

(* ----------------------------------------------------- *)
(* Proto-Reduction Definition                            *)
(* ----------------------------------------------------- *)

Definition proto_reduce (w1 w2 : LMetrics) : Prop :=
  witness_complexity w2 = witness_complexity w1.

(* ----------------------------------------------------- *)
(* Reduced examples                                      *)
(* ----------------------------------------------------- *)

Lemma proto_reduce_P_to_P :
  proto_reduce witness_crit2 witness_crit3.
Proof.
  unfold proto_reduce.
  (* both are P_like *)
  unfold witness_complexity, complexity_bridge, safe_bridge; simpl.
  unfold get_V0; simpl.
  destruct (Rlt_dec 0%R 0%R);
  destruct (Rlt_dec 14%R 0%R);
  reflexivity || exfalso; lra.
Qed.

(* ----------------------------------------------------- *)
(* Impossibile ridurre NP_like in P_like                 *)
(* ----------------------------------------------------- *)

Lemma proto_no_reduce_NP_to_P :
  proto_reduce witness_crit1 witness_crit2 -> False.
Proof.
  unfold proto_reduce.
  unfold witness_complexity, complexity_bridge, safe_bridge; simpl.
  unfold get_V0; simpl.
  destruct (Rlt_dec (-120)%R 0%R);
  destruct (Rlt_dec 14%R 0%R);
  try discriminate; try lra.
Qed.

(* ----------------------------------------------------- *)
(* Chiusura minima                                       *)
(* ----------------------------------------------------- *)

Lemma proto_reduce_ok : True.
Proof. exact I. Qed.

