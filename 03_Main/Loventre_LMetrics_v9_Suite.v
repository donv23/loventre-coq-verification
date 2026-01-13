(*
  ---------------------------------------------------------
  Loventre_LMetrics_v9_Suite.v
  Mini test suite V9 — esistenza di meta-decisioni
  ---------------------------------------------------------
*)

From Stdlib Require Import Reals Bool String.
Open Scope R_scope.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

From Loventre_Main Require Import
     Loventre_Main_Theorem_v9_Prelude
     Loventre_LMetrics_v9_SAFE
     Loventre_LMetrics_v9_Aliases
     Loventre_LMetrics_v9_Policy
     Loventre_LMetrics_v9_Risk
     Loventre_LMetrics_v9_MetaDecision
     Loventre_LMetrics_v9_OneShot
     Loventre_LMetrics_v9_Witness_Package.

Set Implicit Arguments.
Unset Strict Implicit.

(*
  ---------------------------------------------------------
  Helper:
  esegue la pipeline e ritorna MetaDecision
  ---------------------------------------------------------
*)

Definition suite_meta (m : LMetrics) : MetaDecision :=
  loventre_decide_v9_oneshot m.

(*
  ---------------------------------------------------------
  Seed11 — esiste una meta-decisione (costruttivamente)
  ---------------------------------------------------------
*)

Lemma suite_seed11_meta_exists :
  exists d : MetaDecision, d = suite_meta seed11.
Proof. repeat eexists; reflexivity. Qed.

(*
  ---------------------------------------------------------
  2SATcrit — esiste una meta-decisione
  ---------------------------------------------------------
*)

Lemma suite_2satcrit_meta_exists :
  exists d : MetaDecision, d = suite_meta sat2_crit.
Proof. repeat eexists; reflexivity. Qed.

(* End of Suite V9 *)

