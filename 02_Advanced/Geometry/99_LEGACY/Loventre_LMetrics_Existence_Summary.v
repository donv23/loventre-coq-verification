(* ************************************************************** *)
(* Loventre_LMetrics_Existence_Summary.v — Bridge in Geometry     *)
(*   Dicembre 2025                                               *)
(*   Collegamento JSON → LMetrics → predicati P / NP_like_BH      *)
(* ************************************************************** *)

From Stdlib Require Import Reals.

(* LMetrics è definito qui *)
From Loventre_Advanced Require Import Loventre_Metrics_Bus.

(* Witness JSON + predicati di fase *)
From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Phase_Predicates.

Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================= *)
(**  Predicati astratti P-like / NP_like-black-hole               *)
(** ============================================================= *)

Parameter is_P_like : LMetrics -> Prop.
Parameter is_NP_like_black_hole : LMetrics -> Prop.

(** ============================================================= *)
(**  Witness principali (LMetrics)                                *)
(**  Nota: qui li trattiamo come parametri astratti;              *)
(**        in futuro potranno essere legati alle Def esatte       *)
(**        generate dal bridge JSON (m_seed11_cli_demo, ...)      *)
(** ============================================================= *)

Parameter m_seed11_cli_demo    : LMetrics.
Parameter m_seed_grid_demo     : LMetrics.
Parameter m_TSPcrit28_cli_demo : LMetrics.
Parameter m_SATcrit16_cli_demo : LMetrics.

(** ============================================================= *)
(**  Lemmi testimoni — per ora come assiomi (Parameter)           *)
(**  In futuro si potranno dimostrare usando i predicati          *)
(**  concreti in Loventre_LMetrics_Phase_Predicates               *)
(** ============================================================= *)

Parameter m_seed11_soddisfa_is_P_like :
  is_P_like m_seed11_cli_demo.

Parameter m_seed_grid_soddisfa_is_P_like :
  is_P_like m_seed_grid_demo.

Parameter m_TSPcrit28_soddisfa_is_NP_like_black_hole :
  is_NP_like_black_hole m_TSPcrit28_cli_demo.

Parameter m_SATcrit16_soddisfa_is_NP_like_black_hole :
  is_NP_like_black_hole m_SATcrit16_cli_demo.

