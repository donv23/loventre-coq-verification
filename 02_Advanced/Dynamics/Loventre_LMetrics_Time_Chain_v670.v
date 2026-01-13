From Stdlib Require Import ZArith Reals.
From Loventre_Core Require Import
  Loventre_Core_Prelude
  Loventre_Foundation_Types
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
  Loventre_Curvature_Field
  Loventre_Potential_Field
  Loventre_Barrier_Model
  Loventre_Tunneling_Model
  Loventre_Risk_Level
  Loventre_Risk_Level_Bridge
  Loventre_SAFE_Model
  Loventre_Class_Model
  Loventre_Class_Properties
  Loventre_Phase_Assembly
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure.

From Loventre_Advanced.Dynamics Require Import
  Loventre_LMetrics_Time_Model_v600
  Loventre_LMetrics_Time_From_JSON_v610
  Loventre_LMetrics_Time_EvolveN_v620
  Loventre_LMetrics_Time_Collapse_v630
  Loventre_LMetrics_Time_Test_3SAT_v640
  Loventre_LMetrics_Time_Theorem_3SAT_v650
  Loventre_LMetrics_Time_Exact_v660.

Open Scope R_scope.

(** -------------------------------------------------------- *)
(** V670 : Catena dinamica globale                           *)
(** -------------------------------------------------------- *)

(* La traiettoria canonica:
   P_like → P_accessible → NP_blackhole
*)

Lemma Loventre_dynamic_chain_P_to_Pacc :
  forall m1 m2,
    is_P_like m1 ->
    Loventre_evolve_step m1 m2 ->
    is_P_accessible m2.
Proof.
  intros m1 m2 Hpl Hev.
  eapply evolve_preserves_Pacc; eauto.
Qed.

Lemma Loventre_dynamic_chain_Pacc_to_bh :
  forall m1 m2,
    is_P_accessible m1 ->
    Loventre_evolve_step m1 m2 ->
    is_NP_like_blackhole m2.
Proof.
  intros m1 m2 Hp Hev.
  eapply evolve_pushes_to_bh; eauto.
Qed.

Theorem Loventre_chain_P_to_bh :
  forall m0 m1 m2,
    is_P_like m0 ->
    Loventre_evolve_step m0 m1 ->
    Loventre_evolve_step m1 m2 ->
    is_NP_like_blackhole m2.
Proof.
  intros m0 m1 m2 Hpl H01 H12.
  pose proof (Loventre_dynamic_chain_P_to_Pacc m0 m1 Hpl H01) as Hmid.
  eapply Loventre_dynamic_chain_Pacc_to_bh; eauto.
Qed.

(** -------------------------------------------------------- *)
(** Forma parametrica: n passi                               *)
(** -------------------------------------------------------- *)

Theorem Loventre_chain_P_to_bh_n :
  forall n m0 mN,
    is_P_like m0 ->
    Loventre_evolve_n m0 n mN ->
    is_NP_like_blackhole mN.
Proof.
  intros n m0 mN Hpl Hev.
  eapply evolve_n_forces_bh; eauto.
Qed.

(** -------------------------------------------------------- *)
(** Punto: questa è ormai una legge dinamica globale         *)
(** -------------------------------------------------------- *)

(* conclusione:
   le classi non sono isole statiche:
   sono tappe di una traiettoria unidirezionale
*)

