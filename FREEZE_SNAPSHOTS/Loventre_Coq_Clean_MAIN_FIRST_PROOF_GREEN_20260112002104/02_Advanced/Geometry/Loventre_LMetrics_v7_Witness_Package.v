(*
  ---------------------------------------------------------
  Loventre_LMetrics_v7_Witness_Package.v
  Pacchetto witness: JSON → V7 → Bus
  Congelamento: Gennaio 2026
  ---------------------------------------------------------
*)

From Stdlib Require Import Reals String Bool.
Open Scope R_scope.

(* Struttura V7 *)
From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v7_Structure
                    Loventre_LMetrics_v7_JSON_Importer
                    Loventre_LMetrics_v7_JSON_Seeds
                    Loventre_LMetrics_v7_Witness_From_JSON
                    Loventre_LMetrics_v7_Witness_Seeds
                    Loventre_LMetrics_v7_to_Bus.

Import Loventre_LMetrics_V7_Structure.

(* ---- IMPORT BUS CORE ---- *)
From Loventre_Advanced
     Require Import Loventre_Metrics_Bus.

Import Loventre_Metrics_Bus.

(*
  ---------------------------------------------------------
  Bus level: applicazione del traduttore
  ---------------------------------------------------------
*)

Definition bus_seed11 : LMetrics :=
  translate_LMetrics_v7_to_bus m_seed11_v7.

Definition bus_TSPcrit28 : LMetrics :=
  translate_LMetrics_v7_to_bus m_TSPcrit28_v7.

Definition bus_2SAT_easy : LMetrics :=
  translate_LMetrics_v7_to_bus m_2SAT_easy_v7.

Definition bus_2SAT_crit : LMetrics :=
  translate_LMetrics_v7_to_bus m_2SAT_crit_v7.

(*
  ---------------------------------------------------------
  Lemma di copertura bus
  ---------------------------------------------------------
*)

Lemma all_bus_exist :
  exists b1 b2 b3 b4 : LMetrics,
    b1 = bus_seed11 /\
    b2 = bus_TSPcrit28 /\
    b3 = bus_2SAT_easy /\
    b4 = bus_2SAT_crit.
Proof.
  repeat eexists; repeat split; reflexivity.
Qed.

