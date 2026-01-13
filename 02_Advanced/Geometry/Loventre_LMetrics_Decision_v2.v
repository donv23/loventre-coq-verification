(*
  Loventre_LMetrics_Decision_v2.v
  FASE 4.3 — Decisione canonica estesa
  Dicembre 2025
*)

From Stdlib Require Import Reals.
From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Tunneling.

Open Scope R_scope.

(* ======================================================= *)
(* === Tipo di decisione canonico                       === *)
(* ======================================================= *)

Inductive LoventreDecision :=
| DEC_SAFE
| DEC_WARNING
| DEC_BLACKHOLE.

(* ======================================================= *)
(* === Soglie canoniche (parametriche)                  === *)
(* ======================================================= *)

Parameter p_tunnel_min : R.
Parameter P_success_min : R.

Axiom p_tunnel_min_pos : 0 < p_tunnel_min <= 1.
Axiom P_success_min_pos : 0 < P_success_min.

(* ======================================================= *)
(* === Decisione canonica v2                            === *)
(* ======================================================= *)

Definition decision_of_LMetrics_v2 (M : LMetrics) : LoventreDecision :=
  if Rle_dec (p_tunnel M) p_tunnel_min then
    DEC_BLACKHOLE
  else if Rle_dec (P_success M) P_success_min then
    DEC_WARNING
  else
    DEC_SAFE.

