(* ======================================================= *)
(* LOVENTRE ENGINE v7 — CLASSIFY                          *)
(* API ponte coerente con Python v7                       *)
(* ======================================================= *)

From Stdlib Require Import ZArith Bool.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_import
     LMetrics_v7_safe_bh.

(* ------------------------------------------------------- *)
(* Classificazione coerente con Policy v7 Python           *)
(* Versione Coq: restituisce record con 3 campi            *)
(* ------------------------------------------------------- *)

Record L7ClassifyResult := {
  class_v7 : string;
  score_v7 : Z;
  safe_flag : bool
}.

(* Funzione di classificazione minimale lato Coq           *)
(* Python ragiona sul meta_label numerico:                 *)
(* 0 → baseline, 1–3 → weak, >=4 → strong                  *)
(* ------------------------------------------------------- *)
Definition classify (m : LMetricsV7) : L7ClassifyResult :=
  let ml := meta_label m in
  if (ml <? 1)%Z then
      {| class_v7 := "baseline"; score_v7 := ml; safe_flag := true |}
  else if (ml <? 4)%Z then
      {| class_v7 := "weak"; score_v7 := ml; safe_flag := true |}
  else
      {| class_v7 := "strong"; score_v7 := ml; safe_flag := true |}.

(* ------------------------------------------------------- *)
(* Alias API coerente con Python — fix v3.9.0.2            *)
(* ------------------------------------------------------- *)
Definition classify_v7 (m : LMetricsV7) : L7ClassifyResult :=
  classify m.

(* ------------------------------------------------------- *)
(* Fine file CLASSIFY v7                                   *)
(* ------------------------------------------------------- *)

