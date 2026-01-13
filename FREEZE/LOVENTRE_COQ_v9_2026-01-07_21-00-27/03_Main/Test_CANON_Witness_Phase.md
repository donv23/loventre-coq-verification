(**
  Test_CANON_Witness_Phase.v

  Test Coq minimale dei witness CANON esportati dal motore Python.
  File SHADOW: non importato nel CANON principale, non nel Makefile.
*)

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_CANON_Index.

From Loventre_Main.Witnesses.CANON Require Import
  m_seed_1_1
  m_seed_2_2
  m_seed_3_3.

Goal
  is_SAFE m_seed_1_1 \/
  is_WARNING m_seed_1_1 \/
  is_BLACKHOLE m_seed_1_1.
Proof.
  unfold is_WARNING.
  tauto.
Qed.

Goal
  is_SAFE m_seed_2_2 \/
  is_WARNING m_seed_2_2 \/
  is_BLACKHOLE m_seed_2_2.
Proof.
  unfold is_WARNING.
  tauto.
Qed.

Goal
  is_SAFE m_seed_3_3 \/
  is_WARNING m_seed_3_3 \/
  is_BLACKHOLE m_seed_3_3.
Proof.
  unfold is_WARNING.
  tauto.
Qed.

