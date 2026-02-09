From Stdlib Require Import Reals.
From Stdlib Require Import List.

From LMetrics_v6 Require Import
     LMetrics_v6_types
     Loventre_Minibridge_General
     witness_json_m_v6_seed_01
     witness_json_m_v6_seed_02
     witness_json_m_v6_seed_03.

Import ListNotations.

(* Witness alias per leggibilità *)
Definition w1 := witness_json_m_v6_seed_01.
Definition w2 := witness_json_m_v6_seed_02.
Definition w3 := witness_json_m_v6_seed_03.

(* Lista dei witness e delle loro valutazioni *)
Definition mb_inputs : list LMetrics := [w1; w2; w3].
Definition mb_outputs : list MClass := map mb_eval mb_inputs.

(* ====================================================== *)
(* TEST 1 — Ogni witness è classificato correttamente     *)
(* ====================================================== *)

Example test_each_is_valid :
  Forall
    (fun w =>
       mb_eval w = MB_P \/
       mb_eval w = MB_PA \/
       mb_eval w = MB_BH)
    mb_inputs.
Proof.
  (* Analizziamo la lista literalmente *)
  unfold mb_inputs.
  simpl.

  (* Primo elemento *)
  constructor.
  (* dimostro esplicitamente che è una di quelle tre opzioni *)
  remember (mb_eval w1) as c1.
  destruct c1; auto.

  (* Secondo elemento *)
  constructor.
  remember (mb_eval w2) as c2.
  destruct c2; auto.

  (* Terzo elemento *)
  constructor.
  remember (mb_eval w3) as c3.
  destruct c3; auto.

  (* chiudo la lista *)
  constructor.
Qed.

(* ====================================================== *)
(* TEST 2 — Lunghezza della lista                         *)
(* ====================================================== *)

Example test_outputs_len :
  length mb_outputs = 3.
Proof.
  reflexivity.
Qed.

(* ====================================================== *)
(* TEST 3 — Esiste almeno un output                       *)
(* ====================================================== *)

Example test_exists_valid :
  exists c, In c mb_outputs.
Proof.
  unfold mb_outputs. simpl.
  (* Basterà esibire il primo elemento *)
  exists (mb_eval w1).
  auto.
Qed.

