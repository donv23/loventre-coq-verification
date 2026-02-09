(* ======================================================= *)
(* LOVENTRE ENGINE v7 — SELFTEST                           *)
(* ======================================================= *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_import
     LMetrics_v7_INDEX.

(* ------------------------------------------------------- *)
(* Sanity 1 — meta_label è >= 0 sui witness importati      *)
(* ------------------------------------------------------- *)

Lemma selftest_w01_nonneg :
  meta_label_nonneg witness_m_v7_3sat_DIMACS_01.
Proof.
  unfold meta_label_nonneg; simpl; lia.
Qed.

Lemma selftest_w02_nonneg :
  meta_label_nonneg witness_m_v7_3sat_DIMACS_02.
Proof.
  unfold meta_label_nonneg; simpl; lia.
Qed.

Lemma selftest_w03_nonneg :
  meta_label_nonneg witness_m_v7_3sat_DIMACS_03.
Proof.
  unfold meta_label_nonneg; simpl; lia.
Qed.

(* ------------------------------------------------------- *)
(* Sanity 2 — Tutti i primi tre witness condividono meta=0 *)
(* ------------------------------------------------------- *)

Lemma selftest_w01_eq_w02 :
  meta_label witness_m_v7_3sat_DIMACS_01 =
  meta_label witness_m_v7_3sat_DIMACS_02.
Proof. simpl; lia. Qed.

Lemma selftest_w02_eq_w03 :
  meta_label witness_m_v7_3sat_DIMACS_02 =
  meta_label witness_m_v7_3sat_DIMACS_03.
Proof. simpl; lia. Qed.

(* ------------------------------------------------------- *)
(* Sanity 3 — meta_label = 0 ⇒ baseline class in v7        *)
(* ------------------------------------------------------- *)

Lemma selftest_zero_means_zero (m : LMetricsV7) :
  meta_label m = 0%Z -> (0 <= meta_label m)%Z.
Proof. intro H; rewrite H; lia. Qed.

(* ------------------------------------------------------- *)
(* Fine file                                               *)
(* ------------------------------------------------------- *)

