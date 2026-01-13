(*
  Loventre_LMetrics_JSON_Link.v
  V50 — JSON→LMetrics Bridge (fase 1: definizioni)
  Gennaio 2026

  Questo file introduce un record Coq che rappresenta
  un LMetrics proveniente dal mondo Python (V42 canonico).

  Non facciamo parsing JSON in Coq.
  Python fornisce record concreti per i test Coq.
*)

From Coq Require Import String Bool.
Local Open Scope string_scope.
Local Open Scope bool_scope.

(* ---------------------------------------------------------------------- *)
(* TREND / RISK / PROGNOSIS — etichette simboliche                        *)
(* ---------------------------------------------------------------------- *)

Definition trend_tag :=
  String.string.

Definition risk_tag :=
  String.string.

Definition prognosis_tag :=
  String.string.

(* ---------------------------------------------------------------------- *)
(* RECORD LMetrics base per V50                                           *)
(* ---------------------------------------------------------------------- *)

Record LMetricsV50 := mkLMetricsV50 {
  trend_label     : trend_tag ;
  risk_label      : risk_tag ;
  prognosis_label : prognosis_tag ;
  instability_flag : bool ;
  recovery_flag    : bool
}.

(* ---------------------------------------------------------------------- *)
(* FUNZIONI DI SUPPORTO — esempi semplici                                 *)
(* ---------------------------------------------------------------------- *)

Definition is_stable (m : LMetricsV50) : bool :=
  if String.eqb m.(trend_label) "STABLE" then true else false.

Definition is_collapsing (m : LMetricsV50) : bool :=
  if String.eqb m.(trend_label) "COLLAPSING" then true else false.

Definition is_oscillating (m : LMetricsV50) : bool :=
  if String.eqb m.(trend_label) "OSCILLATING" then true else false.

(* rischio HIGH → vero *)
Definition high_risk (m : LMetricsV50) : bool :=
  if String.eqb m.(risk_label) "HIGH" then true else false.

(* prognosi prossima al BH → vera se etichetta critica *)
Definition near_blackhole (m : LMetricsV50) : bool :=
  if String.eqb m.(prognosis_label) "NEAR_BLACKHOLE" then true else false.

(* ---------------------------------------------------------------------- *)
(* SANITY RULES (interne al modello, non ancora teoremi)                 *)
(* ---------------------------------------------------------------------- *)

Definition instability_requires_nonstable (m : LMetricsV50) : bool :=
  if m.(instability_flag)
  then negb (is_stable m)
  else true.

Definition recovery_requires_possible (m : LMetricsV50) : bool :=
  if m.(recovery_flag)
  then negb (near_blackhole m)
  else true.

(* ---------------------------------------------------------------------- *)
(* Fine modulo V50 JSON Bridge (fase 1)                                   *)
(* ---------------------------------------------------------------------- *)

