(** Loventre_Main_Witness_2SAT.v
    Witness aggiuntivi per mostrare pluralità di famiglie
    Versione V58-01 — Gennaio 2026
 *)

From Stdlib Require Import Reals Bool.
From Loventre_Advanced Require Import Loventre_LMetrics_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** ===========================
      Witness 2-SAT v58
    =========================== *)

(** Caso facile: resta nettamente nel regime SAFE *)
Definition m_2SAT_easy_demo : LMetrics :=
  {| kappa_eff := 0.2;
     entropy_eff := 0.25;
     V0 := 1.5;
     horizon_flag := false |}.

(** Caso critico: supera soglia e collassa *)
Definition m_2SAT_crit_demo : LMetrics :=
  {| kappa_eff := 0.9;
     entropy_eff := 1.3;
     V0 := 4.5;
     horizon_flag := true |}.

Close Scope R_scope.

