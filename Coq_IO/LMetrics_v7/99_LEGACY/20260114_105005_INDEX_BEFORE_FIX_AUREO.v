(* ========================================================= *)
(* LOVENTRE ENGINE v7 — LMetrics_v7_INDEX                    *)
(* Aggregatore canonico degli oggetti LMetrics v7            *)
(* ========================================================= *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

(* Carichiamo i tipi principali e Prelude *)
From LMetrics_v7 Require Import LMetrics_v7_Prelude.
From LMetrics_v7 Require Import LMetrics_v7_types.

(* Importiamo TUTTI i witness e i loro nomi da un solo punto *)
From LMetrics_v7 Require Import LMetrics_v7_import.

(*
   Avviso importante:
   In v7, i witness hanno nomi locali definiti in LMetrics_v7_import
   e NON vengono esportati con nomi globali.
   Per questo INDEX non deve definire alias m_v7_*.
*)

(* Sanity lemma sul record *)
Lemma sanity_meta_label_nonneg :
  forall m : LMetricsV7,
    meta_label m >= 0%Z.
Proof. intros m. lia. Qed.

(* End of file *)

