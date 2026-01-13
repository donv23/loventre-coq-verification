(**
  Loventre_Main_Theorem_v8_Test.v
  V8 – Post-Freeze January 2026
  ----------------------------------------------------
  File diagnostico: verifica che i witness passino il
  ponte V7→Bus→Aliases→Interface→Mini senza rompere nulla.

  Nessuna logica nuova.
  Nessuna prova.
  Solo Check e Prints.
*)

From Loventre_Main Require Import
     Loventre_Main_Theorem_v8_Interface.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

(**
  Verifica presenza testimoni V8
*)
Check m_seed11_v8.
Check m_TSPcrit28_v8.
Check m_2SAT_easy_v8.
Check m_2SAT_crit_v8.

(**
  Verifica di un campo del bus
  (non aggiunge logica—solo testimoniale)
*)
Check kappa_eff.
Check entropy_eff.
Check time_regime.

(**
  Verifica che un mappa bus→campo sia visibile
*)
Check (kappa_eff m_seed11_v8).
Check (entropy_eff m_TSPcrit28_v8).

(**
  Punto di ingresso di debug:
  se arrivi qui, tutti i testimoni “vivono” in V8
*)
Print m_seed11_v8.

(* Fine file V8 Test *)

