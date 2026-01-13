(** Loventre_2SAT_LMetrics_Crit_JSON.v
    Profilo critico 2SAT già coerente con LMetrics
    Gennaio 2026 — V84.2.1
 *)

From Stdlib Require Import Reals String Bool.
From Loventre_Core Require Import Loventre_Kernel.
From Loventre_Advanced Require Import Loventre_LMetrics_Core.
From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Structure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** ===========================
        Profilo critico 2SAT
    =========================== *)

(** Non definiamo un record locale nuovo.
    Costruiamo direttamente un LMetrics canonico.
 *)

Definition m_crit : LMetrics :=
  {|
    kappa_eff    := 0.52;
    entropy_eff  := 0.40;
    V0           := 0.35;
    horizon_flag := true
  |}.

Close Scope R_scope.

