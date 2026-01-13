(*
  ---------------------------------------------------------
  Loventre_LMetrics_v9_Witness_From_Bus.v
  Witness minimi V9 — estratti direttamente dal Bus V7/V8
  ---------------------------------------------------------
*)

From Stdlib Require Import Reals String Bool.
Open Scope R_scope.

(* Import bus V7/V8, che definisce LMetrics *)
From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

(*
  ---------------------------------------------------------
  SEED CANONICI V9
  Preleviamo due punti dal bus V7/V8.

  Nota: qui li lasciamo come Parameter, perché
  la loro origine JSON/regime sarà gestita
  nei layer successivi.
  ---------------------------------------------------------
*)

Parameter v9_seed11      : LMetrics.
Parameter v9_2SAT_crit   : LMetrics.

(*
  ---------------------------------------------------------
  Minimal sanity: entrambi sono LMetrics
  (trivialmente veri per costruzione)
  ---------------------------------------------------------
*)

Lemma v9_seed11_is_lmetrics :
  exists m : LMetrics, m = v9_seed11.
Proof. repeat eexists; reflexivity. Qed.

Lemma v9_2SAT_crit_is_lmetrics :
  exists m : LMetrics, m = v9_2SAT_crit.
Proof. repeat eexists; reflexivity. Qed.

(* Fine file Witness_From_Bus V9 *)

