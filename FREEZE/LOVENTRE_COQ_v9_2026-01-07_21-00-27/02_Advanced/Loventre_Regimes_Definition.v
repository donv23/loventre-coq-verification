(** Loventre_Regimes_Definition.v
    Definizioni astratte di regimi dinamici lungo il flusso Loventre. *)

From Stdlib Require Import List Arith ZArith Lia.

Require Import Loventre_Kernel.
Require Import Loventre_Foundation_Types.
Require Import Loventre_Foundation_Time.
Require Import Loventre_Foundation_History_Structure.
Require Import Loventre_Barrier_Model.
Require Import Loventre_Tunneling_Model.
Require Import Loventre_Time_Regimes.
Require Import Loventre_Instance_Profile.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Import Loventre_Geometry.

(** Regimi elementari per stati e tempi *)

Definition regime_subcritical_at (x : State) (n : TimeIndex) : Prop :=
  time_subcritical x n.

Definition regime_supercritical_at (x : State) (n : TimeIndex) : Prop :=
  time_supercritical x n.

Definition regime_under_barrier_at (x : State) (n : TimeIndex) : Prop :=
  under_barrier (Flow n x).

Definition regime_over_barrier_at (x : State) (n : TimeIndex) : Prop :=
  over_barrier (Flow n x).

Definition regime_stable_at (x : State) (n : TimeIndex) : Prop :=
  stable (Flow n x).

Definition regime_divergent_at (x : State) (n : TimeIndex) : Prop :=
  divergent (Flow n x).

(** Regimi globali lungo tutta l'orbita di x *)

Definition permanently_subcritical (x : State) : Prop :=
  forall n : TimeIndex, time_subcritical x n.

Definition permanently_supercritical (x : State) : Prop :=
  forall n : TimeIndex, time_supercritical x n.

Definition permanently_under_barrier (x : State) : Prop :=
  forall n : TimeIndex, under_barrier (Flow n x).

Definition permanently_over_barrier (x : State) : Prop :=
  forall n : TimeIndex, over_barrier (Flow n x).

Definition permanently_stable (x : State) : Prop :=
  forall n : TimeIndex, stable (Flow n x).

Definition permanently_divergent (x : State) : Prop :=
  forall n : TimeIndex, divergent (Flow n x).

(** Transizione critica singola lungo il flusso *)

Definition has_single_critical_transition (x : State) : Prop :=
  exists n_c : TimeIndex, critical_time_candidate x n_c.

(** Regimi su intervalli di tempo finiti *)

Definition regime_subcritical_on_interval
  (x : State) (I : TimeInterval) : Prop :=
  forall n : TimeIndex,
    time_in_interval n I ->
    time_subcritical x n.

Definition regime_supercritical_on_interval
  (x : State) (I : TimeInterval) : Prop :=
  forall n : TimeIndex,
    time_in_interval n I ->
    time_supercritical x n.

Definition regime_under_barrier_on_interval
  (x : State) (I : TimeInterval) : Prop :=
  forall n : TimeIndex,
    time_in_interval n I ->
    under_barrier (Flow n x).

Definition regime_over_barrier_on_interval
  (x : State) (I : TimeInterval) : Prop :=
  forall n : TimeIndex,
    time_in_interval n I ->
    over_barrier (Flow n x).

Definition mixed_regime_on_interval
  (x : State) (I : TimeInterval) : Prop :=
  exists n1 n2 : TimeIndex,
    time_in_interval n1 I /\
    time_in_interval n2 I /\
    time_subcritical x n1 /\
    time_supercritical x n2.

(** Regime di tunneling su un intervallo *)

Definition tunneling_regime_on_interval
  (x : State) (I : TimeInterval) : Prop :=
  exists n_start n_end : TimeIndex,
    time_in_interval n_start I /\
    time_in_interval n_end I /\
    tunneling_crossing x n_start n_end.

(** Regime "oltre barriera" a partire da un indice critico *)

Definition beyond_barrier_regime
  (x : State) (n0 : TimeIndex) : Prop :=
  beyond_barrier_from x n0.

(** Regimi sul profilo di istanza *)

Definition profile_regime_subcritical (p : Instance_Profile) : Prop :=
  profile_subcritical p.

Definition profile_regime_supercritical (p : Instance_Profile) : Prop :=
  profile_supercritical p.

Definition profile_regime_under_barrier (p : Instance_Profile) : Prop :=
  profile_under_barrier p.

Definition profile_regime_over_barrier (p : Instance_Profile) : Prop :=
  profile_over_barrier p.

Definition profile_regime_time_subcritical (p : Instance_Profile) : Prop :=
  profile_time_subcritical p.

Definition profile_regime_time_supercritical (p : Instance_Profile) : Prop :=
  profile_time_supercritical p.

Definition profile_regime_tunneling (p : Instance_Profile) : Prop :=
  exists x : State,
  exists n_start n_end : TimeIndex,
    p = build_profile x n_end /\
    tunneling_crossing x n_start n_end.

(** Tag astratti per i regimi a livello di profilo *)

Inductive Regime_Tag : Type :=
| Regime_Subcritical
| Regime_Supercritical
| Regime_Barrier_Confined
| Regime_Beyond_Barrier
| Regime_Tunneling
| Regime_Mixed.

Definition profile_has_regime (R : Regime_Tag) (p : Instance_Profile) : Prop :=
  match R with
  | Regime_Subcritical =>
      profile_time_subcritical p
  | Regime_Supercritical =>
      profile_time_supercritical p
  | Regime_Barrier_Confined =>
      profile_under_barrier p
  | Regime_Beyond_Barrier =>
      profile_over_barrier p
  | Regime_Tunneling =>
      profile_regime_tunneling p
  | Regime_Mixed =>
      profile_subcritical p \/ profile_supercritical p
  end.

