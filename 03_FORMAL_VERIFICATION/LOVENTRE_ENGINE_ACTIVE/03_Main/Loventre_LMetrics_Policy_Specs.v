(* ======================================================================$
   Loventre_LMetrics_Policy_Specs.v
   -----------------------------------------------------------------------
   Layer: Main (Policy)
   Versione: CANON v3 – senza Axiom
   ----------------------------------------------------------------------- *)

From Stdlib Require Import Reals.
From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_Predicates.

Import Loventre_Metrics_Bus.
Import Loventre_LMetrics_Phase_Predicates.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(* ---------------------------------------------------------------------- *)
(* Enumerazioni di policy                                                 *)
(* ---------------------------------------------------------------------- *)

Inductive GlobalDecision :=
| GD_safe
| GD_borderline
| GD_unsafe.

Inductive GlobalColor :=
| GC_green
| GC_yellow
| GC_red.

(* ---------------------------------------------------------------------- *)
(* Policy functions                                                       *)
(* ---------------------------------------------------------------------- *)

Definition loventre_global_decision (m : LMetrics) : GlobalDecision :=
  if horizon_flag m then GD_unsafe else GD_safe.

Definition loventre_global_color (m : LMetrics) : GlobalColor :=
  match loventre_global_decision m with
  | GD_safe => GC_green
  | GD_borderline => GC_yellow
  | GD_unsafe => GC_red
  end.

(* ---------------------------------------------------------------------- *)
(* Lemmi di coerenza Policy ↔ Phase                                       *)
(* ---------------------------------------------------------------------- *)

Lemma policy_safe_implies_P_like :
  forall m : LMetrics,
    loventre_global_decision m = GD_safe ->
    P_like m.
Proof.
  intros m H.
  unfold P_like, compact_positive, has_horizon.
  unfold loventre_global_decision in H.
  destruct (horizon_flag m) eqn:HF.
  - discriminate.
  - split.
    + intro Contra. destruct Contra as [Hc]. lra.
    + reflexivity.
Qed.

Lemma policy_unsafe_implies_NP_like_black_hole :
  forall m : LMetrics,
    loventre_global_decision m = GD_unsafe ->
    NP_like m.
Proof.
  intros m H.
  unfold NP_like, compact_positive, has_horizon.
  unfold loventre_global_decision in H.
  destruct (horizon_flag m) eqn:HF.
  - split.
    + unfold compact_positive.
      assert (0 < 1)%R by apply Rlt_0_1.
      exact H0.
    + rewrite HF. reflexivity.
  - discriminate.
Qed.

