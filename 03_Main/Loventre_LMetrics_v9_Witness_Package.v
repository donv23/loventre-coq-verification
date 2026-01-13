(*
  ---------------------------------------------------------
  Loventre_LMetrics_v9_Witness_Package.v
  Pacchetto Witness V9 — raccolta e re-export simbolico
  ---------------------------------------------------------
*)

From Stdlib Require Import Reals String Bool.
Open Scope R_scope.

(* Importa il Bus (sorgente del tipo LMetrics) *)
From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

(* Importa i due witness simbolici V9 *)
From Loventre_Main Require Import Loventre_LMetrics_v9_Witness_From_Bus.

(*
  ---------------------------------------------------------
  Obiettivo:
  Offrire un “punto unico” da cui importare i witness
  senza dover referenziare direttamente il Bus.
  ---------------------------------------------------------
*)

Module Loventre_Witness_V9.

  (* Definizione simbolica dei due punti canonici *)
  Definition seed11 : LMetrics := v9_seed11.
  Definition sat2_crit : LMetrics := v9_2SAT_crit.

End Loventre_Witness_V9.

(*
  ---------------------------------------------------------
  Re-export dell’intero modulo per uso globale
  ---------------------------------------------------------
*)
Export Loventre_Witness_V9.

(* Fine file Witness_Package V9 *)

