(* ======================================================= *)
(* LOVENTRE ENGINE v7 — PREDICATES                         *)
(* Classificatori simbolici: P, SAFE, BH, ecc.              *)
(* ======================================================= *)

From Stdlib Require Import Bool ZArith.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_classify
     LMetrics_v7_safe_bh.

(* ------------------------------------------------------- *)
(* P-LIKE = SAFE + classe 'P' o 'EASY'                     *)
(* ------------------------------------------------------- *)
Definition is_P_v7 (m : LMetricsV7) : bool :=
  let c := classify_v7 m in
  let s := safe_bh_v7 m in
  andb s.(flag_safe)
       match c.(class_v7) with
       | "P"   => true
       | "EASY" => true
       | _     => false
       end.

(* ------------------------------------------------------- *)
(* SAFE (stretto) = basta flag                             *)
(* ------------------------------------------------------- *)
Definition is_SAFE_v7 (m : LMetricsV7) : bool :=
  (safe_bh_v7 m).(flag_safe).

(* ------------------------------------------------------- *)
(* BH-like = NON SAFE                                      *)
(* ------------------------------------------------------- *)
Definition is_BH_v7 (m : LMetricsV7) : bool :=
  negb (safe_bh_v7 m).(flag_safe).

(* ------------------------------------------------------- *)
(* Esempio su witness 01                                   *)
(* ------------------------------------------------------- *)
Definition check_safe_w01 : bool :=
  is_SAFE_v7 witness_m_v7_3sat_DIMACS_01.

(* ------------------------------------------------------- *)
(* Fine PREDICATES v7                                      *)
(* ------------------------------------------------------- *)

