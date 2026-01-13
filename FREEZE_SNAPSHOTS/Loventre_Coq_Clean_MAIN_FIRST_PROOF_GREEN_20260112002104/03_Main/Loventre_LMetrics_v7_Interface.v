(*
  Loventre_LMetrics_v7_Interface.v
  Interfaccia pubblica V7 (LMetrics e witness consolidati)
  Congelamento: Gennaio 2026
*)

From Stdlib Require Import Reals String Bool.
Open Scope R_scope.

From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v7_Structure
                    Loventre_LMetrics_v7_JSON_Importer
                    Loventre_LMetrics_v7_JSON_Seeds
                    Loventre_LMetrics_v7_Witness_From_JSON
                    Loventre_LMetrics_v7_Witness_Seeds
                    Loventre_LMetrics_v7_Witness_Package
                    Loventre_LMetrics_v7_to_Bus.

Import Loventre_LMetrics_V7_Structure.

(*
  --------------------------------------------------------------
  Re-export pubblico dei witness V7
  --------------------------------------------------------------
*)

Definition seed11_v7      : LMetrics_v7 := m_seed11_v7.
Definition TSPcrit28_v7   : LMetrics_v7 := m_TSPcrit28_v7.
Definition SATeasy_v7     : LMetrics_v7 := m_2SAT_easy_v7.
Definition SATcrit_v7     : LMetrics_v7 := m_2SAT_crit_v7.

(*
  --------------------------------------------------------------
  Alias leggibili per Test e Main
  --------------------------------------------------------------
*)

Notation m_seed11      := seed11_v7.
Notation m_TSPcrit28   := TSPcrit28_v7.
Notation m_2SAT_easy   := SATeasy_v7.
Notation m_2SAT_crit   := SATcrit_v7.

(*
  Re-export conversione a bus
*)
Definition translate_v7 := translate_LMetrics_v7_to_bus.

