(* ========================================================= *)
(* LOVENTRE ENGINE v7 — LMetrics_v7_INDEX                    *)
(* Entry point dei tipi e dei witness v7                     *)
(* ========================================================= *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

(* Tipi e preludio *)
From LMetrics_v7 Require Import LMetrics_v7_Prelude.
From LMetrics_v7 Require Import LMetrics_v7_types.

(* Import dei witness generati da JSON *)
From LMetrics_v7 Require Import LMetrics_v7_import.

(*
  NOTA TECNICA:
  LMetrics_v7_INDEX è il punto di accesso pubblico v7.

  - NON definisce alias con nomi concreti di witness
  - NON usa alcun riferimento diretto tipo
      witness_json_m_v7_3sat_DIMACS_01

  Tutti i witness vengono caricati come side-effect
  di LMetrics_v7_import.

  Qualsiasi enumerazione, policy o profilo usa i witness
  tramite import-side e NON tramite naming diretto.
*)

Lemma sanity_meta_label_nonneg :
  forall m : LMetricsV7, meta_label m >= 0%Z.
Proof.
  intros m.
  lia.
Qed.

(* Fine del file *)

