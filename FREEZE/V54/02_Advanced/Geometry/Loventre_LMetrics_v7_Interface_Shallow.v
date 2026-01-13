(*
  Loventre_LMetrics_v7_Interface.v
  Interfaccia di consumo per la pipeline V7
  Congelamento: Gennaio 2026
*)

From Stdlib Require Import Reals String Bool.

(* Usa solo il ponte Main → Geometry *)
From Loventre_Main
     Require Import Loventre_LMetrics_v7_Prelude.

(* Rialiasiamo i witness per Main *)
Module LMetrics_V7_Interface.
  Export Loventre_LMetrics_V7_Structure.
  Export Loventre_LMetrics_V7_JSON_Importer.
  Export Loventre_LMetrics_V7_JSON_Seeds.
  Export Loventre_LMetrics_v7_Witness_From_JSON.
  Export Loventre_LMetrics_v7_Witness_Seeds.
  Export Loventre_LMetrics_v7_Witness_Package.
End LMetrics_V7_Interface.

Import LMetrics_V7_Interface.

