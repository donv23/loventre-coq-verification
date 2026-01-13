(** 
  Loventre_Main_Theorem_v8_Prelude.v
  V8 – Post-Freeze January 2026
  --------------------------------
  Questo file costituisce la radice formale della catena V8.
  Non introduce logica nuova.
  Non ridefinisce nulla di V7.
  Si limita a riesportare i moduli strutturali V7 stabiliti 
  come base immutabile della tab V8.
*)

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_v7_Structure
     Loventre_LMetrics_v7_JSON_Importer
     Loventre_LMetrics_v7_JSON_Seeds
     Loventre_LMetrics_v7_Witness_From_JSON
     Loventre_LMetrics_v7_Witness_Seeds
     Loventre_LMetrics_v7_to_Bus
     Loventre_LMetrics_v7_Witness_Package.

(**  Nessun contenuto nuovo.
     Nessuna definizione aggiuntiva.
     Nessun predicato o lemma.
     Questo file esiste soltanto per attestare
     che tutti i moduli V7 sono accessibili dal ramo V8. *)

(* Fine file Prelude V8 *)

