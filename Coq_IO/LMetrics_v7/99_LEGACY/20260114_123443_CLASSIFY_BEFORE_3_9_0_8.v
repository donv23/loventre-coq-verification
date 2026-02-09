(* ======================================================= *)
(* LOVENTRE ENGINE v7 — CLASSIFY                           *)
(* ======================================================= *)

From Stdlib Require Import ZArith Bool String.
Local Open Scope Z_scope.

(* Import core record + SAFE predicate *)
From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_safe_bh.

(* ------------------------------------------------------- *)
(* Classificazione grezza via safe_v7:
     - safe_v7 m = true  -> SAFE
     - safe_v7 m = false -> BH_candidate
   Costruiamo una struttura compatta per esporre il risultato *)
(* ------------------------------------------------------- *)

Record V7ClassifyResult := {
  class_flag : bool;
  class_text : string;
}.

Definition classify_v7 (m : LMetricsV7) : V7ClassifyResult :=
  let sf := safe_v7 m in
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
(* Lemma debole: flag è sempre bool                        *)
(* ------------------------------------------------------- *)
Lemma class_flag_is_bool :
  forall m, class_flag (classify_v7 m) = true \/ class_flag (classify_v7 m) = false.
Proof.
  intro m. unfold classify_v7.
  destruct (safe_v7 m); auto.
Qed.

(* ------------------------------------------------------- *)
(* Fine CLASSIFY                                           *)
(* ------------------------------------------------------- *)

