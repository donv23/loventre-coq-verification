(**
  CANON_State_OK.v

  CHECKPOINT CANONICO DEL MOTORE LOVENTRE

  Questo file congela uno stato coerente in cui:
  - i witness CANON esportati dal motore Python sono validi
  - i predicati di fase CANON sono visibili
  - il typing LMetrics è stabile

  ⚠️ Questo file:
  - NON introduce prove
  - NON entra nel grafo principale
  - NON modifica il makefile
  - Serve solo come checkpoint verificabile

  Dicembre 2025
*)

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_CANON_Index.

From Loventre_Main.Witnesses.CANON Require Import
  m_seed_1_1
  m_seed_2_2
  m_seed_3_3.

(* ================================================= *)
(* === Verifica di typing dei witness CANON       === *)
(* ================================================= *)

Check m_seed_1_1 : LMetrics.
Check m_seed_2_2 : LMetrics.
Check m_seed_3_3 : LMetrics.

(* ================================================= *)
(* === Verifica visibilità predicati di fase       === *)
(* ================================================= *)

Check is_SAFE       : LMetrics -> Prop.
Check is_WARNING    : LMetrics -> Prop.
Check is_BLACKHOLE  : LMetrics -> Prop.

(* ================================================= *)
(* === Fine checkpoint CANON                       === *)
(* ================================================= *)

