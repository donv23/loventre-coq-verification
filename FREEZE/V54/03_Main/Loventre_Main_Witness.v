(** Loventre_Main_Witness.v
    Definizione dei witness per testare le classi interne
    Versione V52 — GENNAIO 2026
 *)

From Stdlib Require Import Reals Bool.
From Loventre_Advanced Require Import Loventre_LMetrics_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** ===========================
      Witness canonici v52
    =========================== *)

(** m_seed_minimal — chiaro caso P_like *)
Definition m_seed_minimal : LMetrics :=
  {| kappa_eff := 0.1;
     entropy_eff := 0.1;
     V0 := 1.0;
     horizon_flag := false |}.

(** m_seed_middle — caso intermedio:
    SAFE ma vicino alla soglia
    → P_accessible_like
 *)
Definition m_seed_middle : LMetrics :=
  {| kappa_eff := 0.4;
     entropy_eff := 0.6;
     V0 := 2.0;
     horizon_flag := false |}.

(** m_seed_critico — oltre la soglia:
    black hole informazionale
 *)
Definition m_seed_critico : LMetrics :=
  {| kappa_eff := 1.2;
     entropy_eff := 1.5;
     V0 := 5.0;
     horizon_flag := true |}.

Close Scope R_scope.

