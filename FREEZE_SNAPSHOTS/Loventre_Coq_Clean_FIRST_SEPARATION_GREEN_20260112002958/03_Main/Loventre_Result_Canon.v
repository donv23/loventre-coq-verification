(*
  Loventre_Result_Canon.v
  Versione: dicembre 2025

  Record canonico del risultato Loventre:
  controparte formale del meta-engine Python.

  File puramente strutturale:
  - nessuna assunzione
  - dipendenze minime
  - namespace coerente con -Q canonici
*)

From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Structure.

(* ============================== *)
(* Tipo astratto del seed         *)
(* ============================== *)

Parameter Seed : Type.

(* ============================== *)
(* Tipo della decisione           *)
(* ============================== *)

Inductive LoventreDecision : Type :=
| SAFE
| WARNING
| CRITICAL
| BLACK_HOLE.

(* ============================== *)
(* Record canonico del risultato  *)
(* ============================== *)

Record LoventreResult : Type := {
  lr_seed     : Seed;
  lr_metrics  : LMetrics;
  lr_decision : LoventreDecision;
}.

