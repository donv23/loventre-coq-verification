(**
  Test_CANON_Phase_Minimal.v

  Test minimale dei predicati di fase CANON
  su witness esportati dal motore Python.

  Dicembre 2025
*)

From Stdlib Require Import Reals Classical.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_CANON_Index.

From Loventre_Main.Witnesses.CANON Require Import
  m_seed_1_1
  m_seed_2_2
  m_seed_3_3.

(* -------------------------------------------------- *)
(* Apertura esplicita del modulo CANON                *)
(* -------------------------------------------------- *)

Import Loventre_LMetrics_Phase_CANON.

(* -------------------------------------------------- *)
(* Verifica di tipo dei witness                       *)
(* -------------------------------------------------- *)

Check m_seed_1_1 : LMetrics.
Check m_seed_2_2 : LMetrics.
Check m_seed_3_3 : LMetrics.

(* -------------------------------------------------- *)
(* Verifica di visibilità dei predicati               *)
(* -------------------------------------------------- *)

Check is_SAFE.
Check is_WARNING.
Check is_BLACKHOLE.

(* -------------------------------------------------- *)
(* Test logico minimale                               *)
(* -------------------------------------------------- *)

Example seed_1_1_is_SAFE_or_not :
  is_SAFE m_seed_1_1 \/ ~ is_SAFE m_seed_1_1.
Proof.
  apply classic.
Qed.

