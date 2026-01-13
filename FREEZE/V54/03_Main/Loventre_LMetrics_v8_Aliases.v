(**
  Loventre_LMetrics_v8_Aliases.v
  V8 – Post-Freeze January 2026
  ----------------------------------------------------
  Alias V7→V8 per i witness sul Bus.
  Si aggancia direttamente a Loventre_LMetrics_v7_Witness_Package.
*)

From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v7_Witness_Package.

(** Alias pubblico V8 per i witness già tradotti nel Bus *)

Notation m_seed11_v8 := bus_seed11.
Notation m_TSPcrit28_v8 := bus_TSPcrit28.
Notation m_2SAT_easy_v8 := bus_2SAT_easy.
Notation m_2SAT_crit_v8 := bus_2SAT_crit.

(* Fine file V8 Aliases *)

