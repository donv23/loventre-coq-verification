(* Witness v6 - Tentativo 4 *)
Require Import LMetrics_v6_types.
From Stdlib Require Import Reals.

Module witness_v6_001_test_t4.

(* Campi coerenti con i tipi definiti in LMetrics_v6_types *)
Definition kappa_eff : R := 3.0.
Definition entropy_eff : R := 0.0.
Definition mass_eff : R := 1.0.
Definition inertial_idx : R := 3.0.
Definition risk_index : nat := 3.           (* ❌ Attenzione: tipo nat, usare intero *)
Definition risk_class := HIGH.
Definition loventre_global_decision := SAFE.
Definition loventre_global_color := GREEN.
Definition loventre_global_score : R := 1.0.
Definition meta_label := meta_v6_seed.
Definition source_file := lmetrics_v6_cli_case_1.json.

End witness_v6_001_test_t4.

