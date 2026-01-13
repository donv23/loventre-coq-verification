(* ============================================================= *)
(*                                                               *)
(*   Loventre_Geometric_Stability_Phase.v                        *)
(*                                                               *)
(*   Stabilità geometrica delle fasi P-like / NP-like            *)
(*                                                               *)
(*   Layer: Geometry                                             *)
(*                                                               *)
(* ============================================================= *)

From Stdlib Require Import Reals.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Phase_Predicates.

Import Loventre_LMetrics_Phase_Predicates.

(* ------------------------------------------------------------- *)
(* Nozione minimale di equivalenza strutturale                   *)
(* ------------------------------------------------------------- *)

Definition same_phase_structure (m1 m2 : Loventre_Metrics_Bus.LMetrics) : Prop :=
  m1.(Loventre_Metrics_Bus.horizon_flag)
    = m2.(Loventre_Metrics_Bus.horizon_flag)
  /\
  m1.(Loventre_Metrics_Bus.chi_compactness)
    = m2.(Loventre_Metrics_Bus.chi_compactness).

(* ------------------------------------------------------------- *)
(* Lemmi di stabilità                                            *)
(* ------------------------------------------------------------- *)

Section Phase_Stability.

  Lemma P_like_stable_under_structure :
    forall m1 m2,
      same_phase_structure m1 m2 ->
      P_like m1 ->
      P_like m2.
  Proof.
    intros m1 m2 [Hh Hc] HP.
    unfold P_like in *.
    destruct HP as [Hnot_compact Hno_horizon].
    split.
    - unfold compact_positive.
      rewrite <- Hc.
      exact Hnot_compact.
    - rewrite <- Hh.
      exact Hno_horizon.
  Qed.

  Lemma NP_like_stable_under_structure :
    forall m1 m2,
      same_phase_structure m1 m2 ->
      NP_like m1 ->
      NP_like m2.
  Proof.
    intros m1 m2 [Hh Hc] HNP.
    unfold NP_like in *.
    destruct HNP as [Hcompact Hhorizon].
    split.
    - unfold compact_positive.
      rewrite <- Hc.
      exact Hcompact.
    - unfold has_horizon in *.
      rewrite <- Hh.
      exact Hhorizon.
  Qed.

End Phase_Stability.

(* ============================================================= *)
(*   FINE FILE                                                   *)
(* ============================================================= *)

