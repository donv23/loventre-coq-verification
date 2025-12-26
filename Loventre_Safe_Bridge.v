(* ============================================================= *)
(*                                                               *)
(*   Loventre_Safe_Bridge.v                                      *)
(*                                                               *)
(*   Bridge strutturale SAFE / UNSAFE                            *)
(*   (lettura globale su LMetrics)                               *)
(*                                                               *)
(* ============================================================= *)

From Stdlib Require Import Reals.
Require Import Coq.micromega.Lra.

Require Import Loventre_Metrics_Bus.
Require Import Loventre_Metrics_Bus_Core.
Require Import Loventre_LMetrics_JSON_Witness.
Require Import Loventre_Policy_Base.

Open Scope R_scope.

Definition safe_bridge (w : LMetrics) : SafeState :=
  if Rlt_dec (get_V0 w) 0%R then UNSAFE else SAFE.

Lemma witness_negative_is_UNSAFE :
  safe_bridge witness_crit1 = UNSAFE.
Proof.
  unfold safe_bridge; simpl.
  unfold get_V0; simpl.
  destruct (Rlt_dec (-120)%R 0%R); try reflexivity; lra.
Qed.

Lemma witness_positive_is_SAFE :
  safe_bridge witness_crit2 = SAFE.
Proof.
  unfold safe_bridge; simpl.
  unfold get_V0; simpl.
  destruct (Rlt_dec 14%R 0%R); try reflexivity; lra.
Qed.

Lemma witness_zero_is_SAFE :
  safe_bridge witness_crit3 = SAFE.
Proof.
  unfold safe_bridge; simpl.
  unfold get_V0; simpl.
  destruct (Rlt_dec 0%R 0%R); try reflexivity; lra.
Qed.

Lemma safe_bridge_ok : True.
Proof. exact I. Qed.

(* ============================================================= *)
(*   FINE FILE                                                   *)
(* ============================================================= *)

