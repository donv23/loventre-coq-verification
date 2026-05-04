(**
  Loventre_LMetrics_JSON_Witness.v
  ===============================================

  Geometry-level witness declarations for the Loventre v3 stack.

  This file must NOT import itself.

  It provides the abstract JSON/metrics witness constants used by:
  - Loventre_LMetrics_Existence_Summary
  - Loventre_LMetrics_Phase_Predicates
  - Loventre_Witness_v3
  - Loventre_Phase_Separation_v3
*)

From Stdlib Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus.

Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Parameter m_seed11_cli_demo : LMetrics.
Parameter m_seed_grid_demo : LMetrics.
Parameter m_TSPcrit28_cli_demo : LMetrics.
Parameter m_SATcrit16_cli_demo : LMetrics.
