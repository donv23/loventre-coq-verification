(* ======================================================= *)
(* LOVENTRE ENGINE v7 — INDEX                             *)
(* ======================================================= *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_import.

(* ------------------------------------------------------- *)
(* Funzione di sanity check sulla meta_label               *)
(* ------------------------------------------------------- *)

Definition meta_label_nonneg (m : LMetricsV7) : Prop :=
  (0 <= meta_label m)%Z.

Lemma sanity_meta_label_nonneg :
  forall m, meta_label_nonneg m.
Proof.
  (* Rimandiamo al V8 per una prova strutturata *)
  Admitted.

(* ------------------------------------------------------- *)
(* Sanity sugli oggetti witness importati                  *)
(* Tutti i json v7 hanno meta_label = 0                    *)
(* ------------------------------------------------------- *)

Lemma sanity_first_witness_nonneg :
  meta_label_nonneg witness_m_v7_3sat_DIMACS_01.
Proof.
  unfold meta_label_nonneg.
  simpl.
  lia.
Qed.

(* ------------------------------------------------------- *)
(* Fine file INDEX                                         *)
(* ------------------------------------------------------- *)

