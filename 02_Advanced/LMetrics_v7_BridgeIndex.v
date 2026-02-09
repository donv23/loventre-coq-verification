(* ====================================================== *)
(* LOVENTRE ENGINE v7 — BridgeIndex                       *)
(* Punto di unione dei 3 bridge: Core, Profile, Policy    *)
(* ====================================================== *)

From Stdlib Require Import ZArith Bool.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
  LMetrics_v7_types
  LMetrics_v7_Prelude
  LMetrics_v7_CoreBridge
  LMetrics_v7_ProfileBridge
  LMetrics_v7_PolicyBridge.

(* Esportiamo l'interfaccia completa del bridge v7 *)

Module LMetricsV7_Bridge.
  Export LMetrics_v7_types.
  Export LMetrics_v7_Prelude.
  Export LMetrics_v7_CoreBridge.
  Export LMetrics_v7_ProfileBridge.
  Export LMetrics_v7_PolicyBridge.
End LMetricsV7_Bridge.

(* Smoke sanity lemma: almeno una policy vale *)
Lemma policy_sanity :
  forall (m : LMetricsV7),
    policy_low m = true \/
    policy_high m = true \/
    policy_baseline m = true.
Proof.
  intro m.
  destruct (policy_low m) eqn:Hlow.
  - left; reflexivity.
  - destruct (policy_high m) eqn:Hhigh.
    + right; left; reflexivity.
    + right; right; reflexivity.
Qed.

(* End of file *)

