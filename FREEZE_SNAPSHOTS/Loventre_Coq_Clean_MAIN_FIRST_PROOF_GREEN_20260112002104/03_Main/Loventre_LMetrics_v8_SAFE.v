(**
  Loventre_LMetrics_v8_SAFE.v
  V8 – Post-Freeze January 2026
  ----------------------------------------------------
  SAFE layer concettuale per V8.
  Nessuna dimostrazione.
  Nessuna derivazione.
  Solo classificazione nominale.

  Tre categorie interne al modello Loventre:
    - P-like (stabile)
    - P-accessible (ponte verso critico)
    - NP-like-black-hole (collasso)
*)

From Loventre_Main Require Import
     Loventre_Main_Theorem_v8_Interface.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

(**
  1. P-like
*)
Definition is_P_like (m : LMetrics) : Prop :=
  m = m_seed11_v8.

(**
  2. P-accessible
*)
Definition is_P_accessible (m : LMetrics) : Prop :=
  m = m_2SAT_easy_v8.

(**
  3. NP-like-black-hole
*)
Definition is_black_hole_like (m : LMetrics) : Prop :=
  m = m_TSPcrit28_v8 \/ m = m_2SAT_crit_v8.

(* Fine SAFE Layer v8 *)

