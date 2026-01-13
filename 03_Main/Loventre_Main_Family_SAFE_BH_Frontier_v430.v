(***************************************************************************)
(* Loventre Main SAFE ↔ BlackHole Frontier Summary — V430                 *)
(***************************************************************************)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import Loventre_Class_Model.
From Loventre_Advanced.Geometry Require Import
  Loventre_Family_SAFE_BH_Frontier_v430
  Loventre_Test_All_2SAT
.

(***************************************************************************)
(* Test: any SAFE witness is NOT BlackHole                                 *)
(***************************************************************************)

Lemma witness_seed_grid_NOT_BH :
  ~ In_NP_blackhole_Loventre m_seed_grid_demo.
Proof.
  apply (SAFE_implies_not_blackhole m_seed_grid_demo).
  exact seed_grid_is_safe.
Qed.

(***************************************************************************)
(* Test: any BlackHole witness is NOT Safe                                 *)
(***************************************************************************)

Lemma witness_TSPcrit28_NOT_SAFE :
  ~ In_Safe_Loventre m_TSPcrit28_cli_demo.
Proof.
  apply (blackhole_implies_not_safe m_TSPcrit28_cli_demo).
  exact TSPcrit28_is_blackhole.
Qed.

(***************************************************************************)
(* Global disjointness                                                     *)
(***************************************************************************)

Theorem family_safe_blackhole_disjoint_global :
  forall M : LMetrics,
    ~ (In_Safe_Loventre M /\ In_NP_blackhole_Loventre M).
Proof.
  apply safe_blackhole_disjoint.
Qed.

