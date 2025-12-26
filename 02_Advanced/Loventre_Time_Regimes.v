From Coq Require Import Arith Lia.
Require Import Loventre_Kernel.

Import Loventre_Geometry.

(** * Time regimes around the critical transition *)

Definition time_subcritical (x : M) (n : nat) : Prop :=
  subcritical (Flow n x).

Definition time_supercritical (x : M) (n : nat) : Prop :=
  supercritical (Flow n x).

Definition subcritical_prefix (x : M) (n_c : nat) : Prop :=
  forall n, (n < n_c)%nat -> time_subcritical x n.

Definition supercritical_suffix (x : M) (n_c : nat) : Prop :=
  forall n, (n >= n_c)%nat -> time_supercritical x n.

Definition critical_time_candidate (x : M) (n_c : nat) : Prop :=
  subcritical_prefix x n_c /\ supercritical_suffix x n_c.

(** Existence of a critical time for every state.
    For now we keep this as an axiom, conceptually corresponding to the
    "Critical_transition" principle from the kernel. *)

Axiom existence_critical_time :
  forall x : M, exists n_c : nat, critical_time_candidate x n_c.

