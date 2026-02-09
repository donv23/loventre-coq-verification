(* ========================================================= *)
(* LOVENTRE ENGINE v7 — LMetrics_v7_INDEX                    *)
(* Entry point dei tipi e dei witness v7                     *)
(* ========================================================= *)

From Stdlib Require Import ZArith Lia List.
Import List.ListNotations.
Local Open Scope Z_scope.

(* Tipi e preludio *)
From LMetrics_v7 Require Import LMetrics_v7_Prelude.
From LMetrics_v7 Require Import LMetrics_v7_types.

(* Import dei witness generati da JSON *)
From LMetrics_v7 Require Import LMetrics_v7_import.

(*
  NOTA TECNICA:
  LMetrics_v7_INDEX è il punto di accesso pubblico v7.

  - NON definisce alias con nomi concreti di witness individuali
  - i witness vengono aggregati tramite all_m_v7_witnesses
*)

Lemma sanity_meta_label_nonneg :
  forall m, In m all_m_v7_witnesses -> meta_label m >= 0%Z.
Proof.
  intros m HIn.
  (* Tutti i witness per ora hanno meta_label 0%Z *)
  simpl in HIn.
  repeat (destruct HIn as [H|HIn]; subst; simpl; lia).
Qed.

(* Fine del file *)

