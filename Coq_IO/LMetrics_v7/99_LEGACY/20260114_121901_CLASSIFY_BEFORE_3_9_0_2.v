(* ======================================================= *)
(* LOVENTRE ENGINE v7 — CLASSIFY                          *)
(* ======================================================= *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

(* Importiamo l'intero layer v7 *)
From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_import
     LMetrics_v7_INDEX.

(* ------------------------------------------------------- *)
(* Classificazione grezza basata su meta_label             *)
(* ------------------------------------------------------- *)

(* Nota: threshold arbitrari micro per V7
   - <= 3  : LOW
   - 4–7   : MID
   - >= 8  : HIGH
   Rifiniremo in V8 in base a SAFE/BH *)
Definition is_low (m : LMetricsV7) : Prop :=
  (meta_label m <= 3)%Z.

Definition is_mid (m : LMetricsV7) : Prop :=
  (4 <= meta_label m <= 7)%Z.

Definition is_high (m : LMetricsV7) : Prop :=
  (8 <= meta_label m)%Z.

(* ------------------------------------------------------- *)
(* Lemmi di compatibilità base                            *)
(* ------------------------------------------------------- *)

Lemma classify_low_or_mid_or_high :
  forall m, is_low m \/ is_mid m \/ is_high m.
Proof.
  intro m.
  unfold is_low, is_mid, is_high.
  destruct (Z_le_gt_dec (meta_label m) 3) as [Hlow | Hgt3].
  - left; lia.
  - right.
    destruct (Z_le_gt_dec (meta_label m) 7) as [Hle7 | Hgt7].
    + left; lia.
    + right; lia.
Qed.

(* ------------------------------------------------------- *)
(* Fine file CLASSIFY                                      *)
(* ------------------------------------------------------- *)

