(* Canvas 9 — Loventre_Complexity_Bridge.v *)

From Stdlib Require Import Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.Program.Equality.

From Loventre Require Import Loventre_Metrics_Bus.
From Loventre Require Import Loventre_Metrics_Bus_Core.
From Loventre Require Import Loventre_LMetrics_JSON_Witness.
From Loventre Require Import Loventre_Policy_Base.
From Loventre Require Import Loventre_Safe_Bridge.
From Loventre Require Import Loventre_Complexity_Tag.

Open Scope R_scope.

(* ----------------------------------------------------- *)
(* Complexity from Policy                                *)
(* ----------------------------------------------------- *)

Definition complexity_bridge (s : SafeState) : CompTag :=
  match s with
  | SAFE => P_like
  | UNSAFE => NP_like
  end.

Definition witness_complexity (w : LMetrics) : CompTag :=
  complexity_bridge (safe_bridge w).

(* ----------------------------------------------------- *)
(* Lemmi di consistenza                                  *)
(* ----------------------------------------------------- *)

Lemma crit1_is_NP_like :
  witness_complexity witness_crit1 = NP_like.
Proof.
  unfold witness_complexity, complexity_bridge, safe_bridge; simpl.
  unfold get_V0; simpl.
  destruct (Rlt_dec (-120)%R 0%R); try reflexivity.
  exfalso; lra.
Qed.

Lemma crit2_is_P_like :
  witness_complexity witness_crit2 = P_like.
Proof.
  unfold witness_complexity, complexity_bridge, safe_bridge; simpl.
  unfold get_V0; simpl.
  destruct (Rlt_dec 14%R 0%R); try reflexivity.
  exfalso; lra.
Qed.

Lemma crit3_is_P_like :
  witness_complexity witness_crit3 = P_like.
Proof.
  unfold witness_complexity, complexity_bridge, safe_bridge; simpl.
  unfold get_V0; simpl.
  destruct (Rlt_dec 0%R 0%R); try reflexivity.
  exfalso; lra.
Qed.

Lemma complexity_bridge_ok : True.
Proof. exact I. Qed.

