(** Loventre_Regimes_Properties.v
    Proprietà elementari dei regimi Loventre. *)

From Stdlib Require Import List Arith ZArith Lia.

Require Import Loventre_Kernel.
Require Import Loventre_Foundation_Types.
Require Import Loventre_Foundation_Time.
Require Import Loventre_Foundation_History_Structure.
Require Import Loventre_Barrier_Model.
Require Import Loventre_Tunneling_Model.
Require Import Loventre_Time_Regimes.
Require Import Loventre_Instance_Profile.
Require Import Loventre_Regimes_Definition.
Require Import Loventre_Lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Import Loventre_Geometry.
Import Loventre_Lemmas.

(* --------------------------------------------------------------- *)
(* 1. Coerenza tra regimi globali e puntuali                      *)
(* --------------------------------------------------------------- *)

Lemma permanently_subcritical_implies_regime_at :
  forall x n,
    permanently_subcritical x ->
    regime_subcritical_at x n.
Proof.
  intros x n H.
  unfold permanently_subcritical, regime_subcritical_at in *.
  apply H.
Qed.

Lemma permanently_supercritical_implies_regime_at :
  forall x n,
    permanently_supercritical x ->
    regime_supercritical_at x n.
Proof.
  intros x n H.
  unfold permanently_supercritical, regime_supercritical_at in *.
  apply H.
Qed.

Lemma permanently_subcritical_not_permanently_supercritical :
  forall x : State,
    permanently_subcritical x ->
    ~ permanently_supercritical x.
Proof.
  intros x Hsub Hsup.
  unfold permanently_subcritical in Hsub.
  unfold permanently_supercritical in Hsup.
  (* guardiamo l'istante 0 *)
  specialize (Hsub 0%nat).
  specialize (Hsup 0%nat).
  unfold regime_subcritical_at, regime_supercritical_at in *.
  unfold time_subcritical, time_supercritical in *.
  (* usiamo la curvatura sullo stato Flow 0 x *)
  eapply subcritical_not_supercritical in Hsub.
  apply Hsub in Hsup.
  exact Hsup.
Qed.

(* --------------------------------------------------------------- *)
(* 2. Regimi su intervalli di tempo                               *)
(* --------------------------------------------------------------- *)

Lemma regime_subcritical_on_interval_mono :
  forall x I1 I2,
    (forall n, time_in_interval n I2 -> time_in_interval n I1) ->
    regime_subcritical_on_interval x I1 ->
    regime_subcritical_on_interval x I2.
Proof.
  intros x I1 I2 Hsubset Hreg n Hn.
  unfold regime_subcritical_on_interval in *.
  apply Hreg.
  apply Hsubset; assumption.
Qed.

Lemma regime_supercritical_on_interval_mono :
  forall x I1 I2,
    (forall n, time_in_interval n I2 -> time_in_interval n I1) ->
    regime_supercritical_on_interval x I1 ->
    regime_supercritical_on_interval x I2.
Proof.
  intros x I1 I2 Hsubset Hreg n Hn.
  unfold regime_supercritical_on_interval in *.
  apply Hreg.
  apply Hsubset; assumption.
Qed.

Lemma permanently_subcritical_implies_subcritical_on_interval :
  forall x I,
    permanently_subcritical x ->
    regime_subcritical_on_interval x I.
Proof.
  intros x I Hperm n _.
  unfold permanently_subcritical in Hperm.
  unfold regime_subcritical_on_interval.
  apply Hperm.
Qed.

Lemma permanently_supercritical_implies_supercritical_on_interval :
  forall x I,
    permanently_supercritical x ->
    regime_supercritical_on_interval x I.
Proof.
  intros x I Hperm n _.
  unfold permanently_supercritical in Hperm.
  unfold regime_supercritical_on_interval.
  apply Hperm.
Qed.

(* --------------------------------------------------------------- *)
(* 3. Regime di tunneling su intervallo                           *)
(* --------------------------------------------------------------- *)

Lemma tunneling_regime_on_interval_implies_has_tunneling :
  forall x I,
    tunneling_regime_on_interval x I ->
    has_tunneling_crossing x.
Proof.
  intros x I H.
  unfold tunneling_regime_on_interval in H.
  destruct H as [n_start [n_end [Hstart [Hend Htc]]]].
  unfold has_tunneling_crossing.
  exists n_start, n_end.
  exact Htc.
Qed.

Lemma tunneling_regime_on_interval_implies_exists_over_barrier_time :
  forall x I,
    tunneling_regime_on_interval x I ->
    exists n,
      time_in_interval n I /\
      over_barrier (Flow n x).
Proof.
  intros x I H.
  unfold tunneling_regime_on_interval in H.
  destruct H as [n_start [n_end [Hstart [Hend Htc]]]].
  exists n_end.
  split; [exact Hend |].
  unfold tunneling_crossing in Htc.
  destruct Htc as [_ [_ Hover]].
  exact Hover.
Qed.

(* --------------------------------------------------------------- *)
(* 4. Esistenza del tempo critico                                 *)
(* --------------------------------------------------------------- *)

Lemma has_single_critical_transition_from_time_regimes :
  forall x : State, has_single_critical_transition x.
Proof.
  intro x.
  unfold has_single_critical_transition.
  apply existence_critical_time.
Qed.

(* --------------------------------------------------------------- *)
(* 5. Regimi di profilo vs regimi puntuali                        *)
(* --------------------------------------------------------------- *)

Lemma profile_regime_subcritical_iff_regime_subcritical_at :
  forall x n,
    regime_subcritical_at x n <-> 
    profile_regime_subcritical (build_profile x n).
Proof.
  intros x n.
  unfold regime_subcritical_at, profile_regime_subcritical.
  unfold profile_subcritical.
  split; intro H.
  - destruct (profile_subcritical_iff_time_subcritical x n) as [_ Hts_to_ps].
    apply Hts_to_ps; exact H.
  - destruct (profile_subcritical_iff_time_subcritical x n) as [Hps_to_ts _].
    apply Hps_to_ts; exact H.
Qed.

Lemma profile_regime_supercritical_iff_regime_supercritical_at :
  forall x n,
    regime_supercritical_at x n <->
    profile_regime_supercritical (build_profile x n).
Proof.
  intros x n.
  unfold regime_supercritical_at, profile_regime_supercritical.
  unfold profile_supercritical.
  split; intro H.
  - destruct (profile_supercritical_iff_time_supercritical x n) as [_ Hts_to_ps].
    apply Hts_to_ps; exact H.
  - destruct (profile_supercritical_iff_time_supercritical x n) as [Hps_to_ts _].
    apply Hps_to_ts; exact H.
Qed.

Lemma profile_regime_under_barrier_iff_regime_under_barrier_at :
  forall x n,
    regime_under_barrier_at x n <->
    profile_regime_under_barrier (build_profile x n).
Proof.
  intros x n; split; intro H.
  - unfold regime_under_barrier_at in H.
    unfold profile_regime_under_barrier.
    unfold profile_under_barrier.
    rewrite (profile_state_is_flow x n).
    exact H.
  - unfold regime_under_barrier_at.
    unfold profile_regime_under_barrier in H.
    unfold profile_under_barrier in H.
    rewrite (profile_state_is_flow x n) in H.
    exact H.
Qed.

Lemma profile_regime_over_barrier_iff_regime_over_barrier_at :
  forall x n,
    regime_over_barrier_at x n <->
    profile_regime_over_barrier (build_profile x n).
Proof.
  intros x n; split; intro H.
  - unfold regime_over_barrier_at in H.
    unfold profile_regime_over_barrier.
    unfold profile_over_barrier.
    rewrite (profile_state_is_flow x n).
    exact H.
  - unfold regime_over_barrier_at.
    unfold profile_regime_over_barrier in H.
    unfold profile_over_barrier in H.
    rewrite (profile_state_is_flow x n) in H.
    exact H.
Qed.

