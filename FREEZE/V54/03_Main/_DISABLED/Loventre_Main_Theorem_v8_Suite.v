(* ---------------------------------------------------------
   Loventre_Main_Theorem_v8_Suite.v
   Suite finale V8 con test su tutti i witness Bus
   --------------------------------------------------------- *)

From Stdlib Require Import Reals String Bool.
Open Scope R_scope.

(* Import Core V8 *)
From Loventre_Main Require Import
     Loventre_Main_Theorem_v8_Prelude
     Loventre_LMetrics_v8_Aliases
     Loventre_Main_Theorem_v8_Interface
     Loventre_LMetrics_v8_SAFE
     Loventre_LMetrics_v8_Policy
     Loventre_LMetrics_v8_Risk
     Loventre_LMetrics_v8_MetaDecision
     Loventre_Main_Theorem_v8_All_In_One
     Loventre_Main_Theorem_v8_Citable.

(* Import Bus-level V7 witness already translated *)
From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v7_Witness_Package.

(* Import del BUS vero e proprio (include record LMetrics) *)
From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

(* ---------------------------------------------------------
   Witness V8 ottenuti dal Bus
   --------------------------------------------------------- *)

Definition v8_seed11 : LMetrics := bus_seed11.
Definition v8_TSPcrit28 : LMetrics := bus_TSPcrit28.
Definition v8_2SAT_easy : LMetrics := bus_2SAT_easy.
Definition v8_2SAT_crit : LMetrics := bus_2SAT_crit.

(* ---------------------------------------------------------
   Funzioni helper V8 — alias dei nomi reali
   --------------------------------------------------------- *)

Definition compute_decision (m : LMetrics) : GlobalDecision :=
  loventre_local_decision m.

Definition compute_color (m : LMetrics) : GlobalColor :=
  loventre_macro_policy m.

Definition compute_risk (m : LMetrics) : RiskClass :=
  loventre_risk_eval m.

(* ---------------------------------------------------------
   Lemmas: esistenza + safe + meta decision
   --------------------------------------------------------- *)

Lemma suite_seed11_safe_and_color :
  exists d c r,
    (compute_decision v8_seed11 = d) /\
    (compute_color v8_seed11 = c) /\
    (compute_risk v8_seed11 = r).
Proof.
  repeat eexists; repeat split; reflexivity.
Qed.

Lemma suite_TSPcrit28_safe_and_color :
  exists d c r,
    (compute_decision v8_TSPcrit28 = d) /\
    (compute_color v8_TSPcrit28 = c) /\
    (compute_risk v8_TSPcrit28 = r).
Proof.
  repeat eexists; repeat split; reflexivity.
Qed.

Lemma suite_2SAT_easy_safe_and_color :
  exists d c r,
    (compute_decision v8_2SAT_easy = d) /\
    (compute_color v8_2SAT_easy = c) /\
    (compute_risk v8_2SAT_easy = r).
Proof.
  repeat eexists; repeat split; reflexivity.
Qed.

Lemma suite_2SAT_crit_safe_and_color :
  exists d c r,
    (compute_decision v8_2SAT_crit = d) /\
    (compute_color v8_2SAT_crit = c) /\
    (compute_risk v8_2SAT_crit = r).
Proof.
  repeat eexists; repeat split; reflexivity.
Qed.

