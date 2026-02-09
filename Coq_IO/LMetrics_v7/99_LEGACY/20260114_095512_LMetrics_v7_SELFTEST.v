From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

(* Importiamo tutto il pacchetto v7 *)
From LMetrics_v7 Require Import
  LMetrics_v7_Prelude
  LMetrics_v7_types
  LMetrics_v7_import.

(* Witness canonico, nome corretto *)
Definition pick_any : LMetricsV7 :=
  witness_m_v7_3sat_DIMACS_01.

(* Verifica sui campi *)
Lemma test_field_types :
  kappa_eff pick_any >= 0 /\
  entropy_eff pick_any >= 0 /\
  V0 pick_any >= 0.
Proof.
  repeat split; compute; try lia.
Qed.

(* Struttura record coerente *)
Lemma test_constructed :
  match pick_any with
  | Build_LMetricsV7 _ _ _ _ _ _ => True
  end.
Proof. exact I. Qed.

(* Import OK *)
Lemma test_imports_ok :
  True.
Proof. exact I. Qed.

