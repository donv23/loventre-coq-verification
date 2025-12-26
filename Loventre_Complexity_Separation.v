(* Canvas 10 — Loventre_Complexity_Separation.v *)

From Stdlib Require Import Reals.
Require Import Coq.micromega.Lra.

From Loventre Require Import Loventre_Metrics_Bus.
From Loventre Require Import Loventre_Metrics_Bus_Core.
From Loventre Require Import Loventre_LMetrics_JSON_Witness.
From Loventre Require Import Loventre_Policy_Base.
From Loventre Require Import Loventre_Safe_Bridge.
From Loventre Require Import Loventre_Complexity_Tag.
From Loventre Require Import Loventre_Complexity_Bridge.

Open Scope R_scope.

(* ----------------------------------------------------- *)
(* Proto-Separazione                                      *)
(* ----------------------------------------------------- *)

Lemma proto_separation :
  exists w1, exists w2,
      witness_complexity w1 = NP_like
  /\  witness_complexity w2 = P_like.
Proof.
  exists witness_crit1.
  exists witness_crit2.
  split.
  - (* crit1 -> NP_like *)
    unfold witness_complexity, complexity_bridge, safe_bridge; simpl.
    unfold get_V0; simpl.
    destruct (Rlt_dec (-120)%R 0%R); try reflexivity.
    exfalso; lra.
  - (* crit2 -> P_like *)
    unfold witness_complexity, complexity_bridge, safe_bridge; simpl.
    unfold get_V0; simpl.
    destruct (Rlt_dec 14%R 0%R); try reflexivity.
    exfalso; lra.
Qed.

(* ----------------------------------------------------- *)
(* Versione compatta                                     *)
(* ----------------------------------------------------- *)

Lemma proto_separation_compact :
  witness_complexity witness_crit1 <> witness_complexity witness_crit2.
Proof.
  unfold witness_complexity, complexity_bridge, safe_bridge; simpl.
  unfold get_V0; simpl.
  destruct (Rlt_dec (-120)%R 0%R);
  destruct (Rlt_dec 14%R 0%R); simpl; try discriminate; try lra.
Qed.

(* ----------------------------------------------------- *)
(* Chiusura minima                                       *)
(* ----------------------------------------------------- *)

Lemma proto_separation_ok : True.
Proof. exact I. Qed.

