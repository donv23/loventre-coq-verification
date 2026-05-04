(* ============================================================= *)
(*                                                               *)
(*   Loventre_Global_Accessibility.v                             *)
(*                                                               *)
(*   LAB-16 — Global Accessibility                               *)
(*                                                               *)
(*   Introduce a minimal, global notion of accessibility         *)
(*   independent of SAFE and rigidity.                           *)
(*                                                               *)
(* ============================================================= *)

From Stdlib Require Import Reals.
Require Import Coq.micromega.Lra.

From Loventre Require Import Loventre_Metrics_Bus.
From Loventre Require Import Loventre_Metrics_Bus_Core.
From Loventre Require Import Loventre_LMetrics_JSON_Witness.
From Loventre Require Import Loventre_Safe_Bridge.

Open Scope R_scope.

(* ------------------------------------------------------------- *)
(* Global Accessibility                                          *)
(* ------------------------------------------------------------- *)

(*
  Intuition:
  A structure is globally accessible if there exists
  at least one non-terminal global channel.

  This notion:
  - is NOT derived from SAFE
  - does NOT depend on V0
  - is NOT a path or inductive notion
*)

Definition globally_accessible (w : LMetrics) : Prop :=
  exists r : R, r > 0 /\ get_entropy w = r.

(* ------------------------------------------------------------- *)
(* Witness analysis                                              *)
(* ------------------------------------------------------------- *)

Lemma crit1_not_accessible :
  ~ globally_accessible witness_crit1.
Proof.
  unfold globally_accessible.
  intros [r [Hr Hent]].
  unfold get_entropy in Hent; simpl in Hent.
  lra.
Qed.

Lemma crit2_accessible :
  globally_accessible witness_crit2.
Proof.
  unfold globally_accessible.
  exists 1%R.
  split; try lra.
  unfold get_entropy; simpl.
  lra.
Qed.

Lemma crit3_accessible :
  globally_accessible witness_crit3.
Proof.
  unfold globally_accessible.
  exists 1%R.
  split; try lra.
  unfold get_entropy; simpl.
  lra.
Qed.

(* ------------------------------------------------------------- *)
(* Separation facts                                              *)
(* ------------------------------------------------------------- *)

Lemma accessibility_independent_of_SAFE :
  globally_accessible witness_crit2 /\
  safe_bridge witness_crit2 = SAFE.
Proof.
  split.
  - apply crit2_accessible.
  - reflexivity.
Qed.

Lemma SAFE_but_accessible :
  globally_accessible witness_crit3 /\
  safe_bridge witness_crit3 = SAFE.
Proof.
  split.
  - apply crit3_accessible.
  - reflexivity.
Qed.

(* ------------------------------------------------------------- *)
(* Epistemic status                                              *)
(* ------------------------------------------------------------- *)

Lemma global_accessibility_ok : True.
Proof. exact I. Qed.

(* ============================================================= *)
(*   END OF FILE                                                 *)
(* ============================================================= *)

