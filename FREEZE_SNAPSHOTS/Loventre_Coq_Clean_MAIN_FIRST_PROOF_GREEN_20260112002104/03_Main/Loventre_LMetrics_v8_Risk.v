(**
  ------------------------------------------------------------------
  Loventre_LMetrics_v8_Risk.v
  Strato Risk fisico nominale — Canvas 10 (Gennaio 2026)
  ------------------------------------------------------------------
  Definisce tre indicatori di rischio basati su valori del Bus:
    - risk_barrier   : barriera V0 vs curvatura kappa
    - risk_tunnel    : tunneling p_tunnel vs P_success
    - risk_load      : entropia vs curvatura
  Più un aggregatore minimale risk_physical.
*)

From Stdlib Require Import Reals.
Open Scope R_scope.

From Loventre_Main
     Require Import
       Loventre_Main_Theorem_v8_Prelude
       Loventre_LMetrics_v8_Aliases.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Unset Strict Implicit.

(**
  1. Rischio barriera
     HIGH se barriera V0 bassa rispetto alla curvatura
*)
Definition risk_barrier (m : LMetrics) : RiskClass :=
  if Rlt_dec (V0 m) (kappa_eff m)
  then RISK_HIGH
  else RISK_MEDIUM.

(**
  2. Rischio tunneling
     HIGH se la probabilità di successo è inferiore al tunneling
*)
Definition risk_tunnel (m : LMetrics) : RiskClass :=
  if Rlt_dec (P_success m) (p_tunnel m)
  then RISK_HIGH
  else RISK_LOW.

(**
  3. Rischio carico (entropia vs curvatura)
     MEDIUM se entropia >= curvatura, LOW altrimenti
*)
Definition risk_load (m : LMetrics) : RiskClass :=
  if Rlt_dec (kappa_eff m) (entropy_eff m)
  then RISK_MEDIUM
  else RISK_LOW.

(**
  4. Aggregazione — nominale
     Se qualsiasi componente è HIGH → HIGH
     Se almeno una è MEDIUM → MEDIUM
     Altrimenti → LOW
*)
Definition risk_physical (m : LMetrics) : RiskClass :=
  match risk_barrier m, risk_tunnel m, risk_load m with
  | RISK_HIGH, _, _ => RISK_HIGH
  | _, RISK_HIGH, _ => RISK_HIGH
  | _, _, RISK_HIGH => RISK_HIGH
  | RISK_MEDIUM, _, _ => RISK_MEDIUM
  | _, RISK_MEDIUM, _ => RISK_MEDIUM
  | _, _, RISK_MEDIUM => RISK_MEDIUM
  | _, _, _ => RISK_LOW
  end.

(* Fine file Risk nominale V8 *)

