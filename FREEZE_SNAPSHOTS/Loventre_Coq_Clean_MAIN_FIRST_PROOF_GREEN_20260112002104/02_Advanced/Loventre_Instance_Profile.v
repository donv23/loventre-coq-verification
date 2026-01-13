(** Loventre_Instance_Profile.v
    Profilo di istanza lungo il flusso Loventre. *)

From Stdlib Require Import ZArith.

Require Import Loventre_Kernel.
Require Import Loventre_Foundation_Types.
Require Import Loventre_Foundation_Entropy.
Require Import Loventre_Potential_Field.
Require Import Loventre_Mass_Equivalence.
Require Import Loventre_Curvature_Field.
Require Import Loventre_Time_Regimes.
Require Import Loventre_Barrier_Model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

Open Scope Z_scope.

Record Instance_Profile := {
  ip_base      : State;
  ip_time      : TimeIndex;
  ip_state     : State;
  ip_kappa     : Z;
  ip_entropy   : Z;
  ip_potential : Z;
  ip_mass      : Z
}.

Definition build_profile (x : State) (n : TimeIndex) : Instance_Profile :=
  {|
    ip_base      := x;
    ip_time      := n;
    ip_state     := Flow n x;
    ip_kappa     := kappa_L   (Flow n x);
    ip_entropy   := Entropy_L (Flow n x);
    ip_potential := U_L       (Flow n x);
    ip_mass      := mass_L    (Flow n x)
  |}.

(** Predicati di regime sul profilo *)

Definition profile_subcritical (p : Instance_Profile) : Prop :=
  curvature_subcritical (ip_state p).

Definition profile_supercritical (p : Instance_Profile) : Prop :=
  curvature_supercritical (ip_state p).

Definition profile_under_barrier (p : Instance_Profile) : Prop :=
  under_barrier (ip_state p).

Definition profile_over_barrier (p : Instance_Profile) : Prop :=
  over_barrier (ip_state p).

Definition profile_time_subcritical (p : Instance_Profile) : Prop :=
  time_subcritical (ip_base p) (ip_time p).

Definition profile_time_supercritical (p : Instance_Profile) : Prop :=
  time_supercritical (ip_base p) (ip_time p).

(** Lemmi di coerenza tra profilo e flusso *)

Lemma profile_state_is_flow :
  forall x n,
    ip_state (build_profile x n) = Flow n x.
Proof.
  intros x n.
  unfold build_profile.
  simpl.
  reflexivity.
Qed.

Lemma profile_subcritical_iff_time_subcritical :
  forall x n,
    profile_subcritical (build_profile x n) <->
    time_subcritical x n.
Proof.
  intros x n.
  unfold profile_subcritical, time_subcritical.
  unfold build_profile.
  simpl.
  unfold curvature_subcritical.
  split; intro H; exact H.
Qed.

Lemma profile_supercritical_iff_time_supercritical :
  forall x n,
    profile_supercritical (build_profile x n) <->
    time_supercritical x n.
Proof.
  intros x n.
  unfold profile_supercritical, time_supercritical.
  unfold build_profile.
  simpl.
  unfold curvature_supercritical.
  split; intro H; exact H.
Qed.

