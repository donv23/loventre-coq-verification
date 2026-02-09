From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

(** Importiamo SOLO il ponte, che già include tutto: tipo + witness *)
From LMetrics_v7 Require Import
  LMetrics_v7_import.

(** Pick canonico di un witness — si compila SE import funziona *)
Definition pick_any : LMetricsV7 :=
  witness_m_v7_3sat_DIMACS_01.

(** Controllo tipi base e campi >= 0 *)
Lemma test_field_types :
  kappa_eff pick_any >= 0 /\
  entropy_eff pick_any >= 0 /\
  V0 pick_any >= 0.
Proof.
  repeat split; compute; try lia.
Qed.

(** Verifica che il record non collassi *)
Lemma test_constructed :
  match pick_any with
  | Build_LMetricsV7 _ _ _ _ _ _ => True
  end.
Proof. exact I. Qed.

(** Dummy sanity: import carica tutto *)
Lemma test_imports_ok :
  True.
Proof. exact I. Qed.

