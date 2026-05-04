(* Loventre_LMetrics_Policy_Specs.v — CANON v3 *)

From Stdlib Require Import Reals Bool.
From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_LMetrics_Phase_Predicates.

Import Loventre_Metrics_Bus.
Import Loventre_LMetrics_Phase_Predicates.Loventre_LMetrics_Phase_Predicates.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Definition loventre_policy_decision (m : LMetrics) : bool :=
  negb (horizon_flag m).

(* ----------------------------------------------------------------- *)
(* Lemma di onestà: la policy garantisce ESATTAMENTE l'assenza di    *)
(* orizzonte (horizon_flag = false). Per concludere is_P_like serve  *)
(* l'ipotesi aggiuntiva ~ compact_positive m.                        *)
(* ----------------------------------------------------------------- *)

Lemma policy_safe_iff_no_horizon :
  forall m : LMetrics,
    loventre_policy_decision m = true <-> horizon_flag m = false.
Proof.
  intros m. unfold loventre_policy_decision. split.
  - intro H. apply negb_true_iff in H. exact H.
  - intro H. rewrite H. reflexivity.
Qed.

Lemma policy_unsafe_iff_horizon :
  forall m : LMetrics,
    loventre_policy_decision m = false <-> horizon_flag m = true.
Proof.
  intros m. unfold loventre_policy_decision. split.
  - intro H. apply negb_false_iff in H. exact H.
  - intro H. rewrite H. reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(* Lemmi originali, ora dimostrati con ipotesi aggiuntiva esplicita  *)
(* sulla compact_positive (necessaria per chiudere is_P_like).       *)
(* ----------------------------------------------------------------- *)

Lemma policy_safe_implies_P_like :
  forall m : LMetrics,
    loventre_policy_decision m = true ->
    ~ compact_positive m ->
    is_P_like m.
Proof.
  intros m Hpol Hncomp.
  unfold is_P_like. split.
  - exact Hncomp.
  - apply policy_safe_iff_no_horizon. exact Hpol.
Qed.

Lemma policy_unsafe_implies_NP_like_black_hole :
  forall m : LMetrics,
    loventre_policy_decision m = false ->
    compact_positive m ->
    risk_class m = risk_np_like_black_hole ->
    is_NP_like_black_hole m.
Proof.
  intros m Hpol Hcomp Hrisk.
  unfold is_NP_like_black_hole, is_NP_like, has_horizon.
  split.
  - split.
    + exact Hcomp.
    + apply policy_unsafe_iff_horizon. exact Hpol.
  - exact Hrisk.
Qed.

(* Stub mantenuto per compatibilità con Theorem_v3_Seed *)
Definition Loventre_Policy_Core_Program : Prop := True.
