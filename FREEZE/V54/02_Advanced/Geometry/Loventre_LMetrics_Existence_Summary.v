(*
  Loventre_LMetrics_Existence_Summary.v
  Geometry Bridge v3+
  Dicembre 2025

  Collegamento:
    LMetrics (Geometry) →
    predicati di fase →
    witness canonici (astratti)

  Nessuna pretesa su P vs NP classico.
*)

From Stdlib Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_Metrics_Bus
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_JSON_Witness.

Import Loventre_Metrics_Bus.
Import Loventre_LMetrics_Phase_Predicates.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(* ============================================================= *)
(* === Predicati astratti di classificazione finale            === *)
(* ============================================================= *)

Parameter is_P_like : LMetrics -> Prop.
Parameter is_NP_like_black_hole : LMetrics -> Prop.

(* ============================================================= *)
(* === Witness canonici (bridge astratto)                      === *)
(* ============================================================= *)

Parameter m_seed11_cli_demo    : LMetrics.
Parameter m_seed_grid_demo     : LMetrics.
Parameter m_TSPcrit28_cli_demo : LMetrics.
Parameter m_SATcrit16_cli_demo : LMetrics.

(* ============================================================= *)
(* === Assiomi di classificazione (bridge dichiarativo)        === *)
(* ============================================================= *)

Axiom m_seed11_soddisfa_is_P_like :
  is_P_like m_seed11_cli_demo.

Axiom m_seed_grid_soddisfa_is_P_like :
  is_P_like m_seed_grid_demo.

Axiom m_TSPcrit28_soddisfa_is_NP_like_black_hole :
  is_NP_like_black_hole m_TSPcrit28_cli_demo.

Axiom m_SATcrit16_soddisfa_is_NP_like_black_hole :
  is_NP_like_black_hole m_SATcrit16_cli_demo.

