(* ======================================================= *)
(* LOVENTRE ENGINE v7 — CLASSIFY                           *)
(* ======================================================= *)

From Stdlib Require Import ZArith Bool String.
Local Open Scope Z_scope.

(* Import core record + helper *)
From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_safe_bh.

(* ------------------------------------------------------- *)
(* Classificazione grezza:
     - safe_flag  = true  -> SAFE
     - safe_flag  = false -> BH_candidate
   La classe testuale viene ora costruita da bool           *)
(* ------------------------------------------------------- *)

Record V7ClassifyResult := {
  class_flag : bool;
  class_text : string;
}.

Definition classify_v7 (m : LMetricsV7) : V7ClassifyResult :=
  let sf := safe_flag m in
  if sf then
    {| class_flag := true;
       class_text := "SAFE" |}
  else
    {| class_flag := false;
       class_text := "BH_candidate" |}.

(* ------------------------------------------------------- *)
(* Esempio su witness01                                    *)
(* ------------------------------------------------------- *)
Definition classify_w01 : V7ClassifyResult :=
  classify_v7 witness_m_v7_3sat_DIMACS_01.

(* ------------------------------------------------------- *)
(* Lemma debole: flag è vero/ falso                        *)
(* ------------------------------------------------------- *)
Lemma class_flag_is_bool :
  forall m, class_flag (classify_v7 m) = true \/ class_flag (classify_v7 m) = false.
Proof.
  intro m. unfold classify_v7.
  destruct (safe_flag m); auto.
Qed.

(* ------------------------------------------------------- *)
(* Fine CLASSIFY                                           *)
(* ------------------------------------------------------- *)

