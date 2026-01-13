(** Loventre_2SAT_LMetrics_From_JSON.v
    Import LMetrics easy 2SAT (aligned to 4-field model)
    Gennaio 2026 — V84.2.7
 *)

From Stdlib Require Import Reals String Bool.
From Loventre_Core Require Import Loventre_Kernel.
From Loventre_Advanced Require Import Loventre_LMetrics_Core.
From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Structure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(* Easy profile — internal representation *)
Record LMetrics_Easy_2SAT := {
  e_kappa_eff   : R;
  e_entropy_eff : R;
  e_V0          : R;
  e_horizon     : bool
}.

(* Embed easy → canonical LMetrics (4-field model) *)
Definition to_LMetrics_easy (w : LMetrics_Easy_2SAT) : LMetrics :=
  {|
    kappa_eff    := e_kappa_eff w;
    entropy_eff  := e_entropy_eff w;
    V0           := e_V0 w;
    horizon_flag := e_horizon w
  |}.

(* Placeholder easy instance *)
Definition m_easy : LMetrics :=
  to_LMetrics_easy
    {|
      e_kappa_eff   := 0.30;
      e_entropy_eff := 0.15;
      e_V0          := 0.10;
      e_horizon     := false
    |}.

Close Scope R_scope.

