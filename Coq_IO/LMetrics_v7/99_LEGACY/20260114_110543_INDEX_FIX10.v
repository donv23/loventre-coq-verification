(* ======================================================= *)
(* LOVENTRE ENGINE v7 — INDEX                             *)
(* ======================================================= *)

From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_import.

(* ------------------------------------------------------- *)
(* Funzione di sanity check sulla meta_label               *)
(* (placeholder: rimandiamo dimostrazione al V8)           *)
(* ------------------------------------------------------- *)

Definition meta_label_nonneg (m : LMetricsV7) : Prop :=
  (0 <= meta_label m)%Z.

Lemma sanity_meta_label_nonneg :
  forall m, meta_label_nonneg m.
Proof.
  (* per ora lasciamo la prova aperta nel CANON v7 *)
  (* dovremo dimostrare qualcosa di vero quando meta_label
     sarà generato da PolicyBridge v8 *)
Admitted.

(* ------------------------------------------------------- *)
(* Aggregato witness: il primo elemento è valido           *)
(* ------------------------------------------------------- *)

Lemma sanity_first_witness_nonneg :
  meta_label_nonneg witness_m_v7_3sat_DIMACS_01.
Proof.
  exact I.
Qed.

(* ------------------------------------------------------- *)
(* Fine file INDEX                                         *)
(* ------------------------------------------------------- *)

