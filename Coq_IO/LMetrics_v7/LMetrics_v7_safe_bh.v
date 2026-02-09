(* ======================================================= *)
(* LOVENTRE ENGINE v7 — SAFE / BLACK-HOLE LAYER            *)
(* ======================================================= *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_import
     LMetrics_v7_INDEX.

(* ------------------------------------------------------- *)
(* Definizioni SAFE / BH in termini di meta_label          *)
(* ------------------------------------------------------- *)
(* Nota v7:
   - meta_label = 0  → profilo "baseline"
   - meta_label = 3  → profilo "weak"
   - meta_label = 9  → profilo "strong"
   Nel layer v7 SAFE/BH usiamo solo questi tre valori
   come casi canonici.
 *)

Definition is_SAFE (m : LMetricsV7) : Prop :=
  meta_label m = 0%Z \/ meta_label m = 3%Z.

Definition is_BH (m : LMetricsV7) : Prop :=
  meta_label m = 9%Z.

(* ------------------------------------------------------- *)
(* Lemmi strutturali di separazione                        *)
(* ------------------------------------------------------- *)

Lemma SAFE_not_BH :
  forall m, is_SAFE m -> is_BH m -> False.
Proof.
  intros m Hs Hbh.
  unfold is_SAFE in Hs.
  unfold is_BH in Hbh.
  destruct Hs as [Hzero | Hthree]; subst; congruence.
Qed.

Lemma BH_not_SAFE :
  forall m, is_BH m -> is_SAFE m -> False.
Proof.
  intros m Hbh Hs.
  eapply SAFE_not_BH; eauto.
Qed.

(* Versione logica equivalente: SAFE e BH non possono
   valere contemporaneamente sullo stesso m. *)
Lemma SAFE_and_BH_contradiction :
  forall m, is_SAFE m /\ is_BH m -> False.
Proof.
  intros m [Hs Hbh].
  eapply SAFE_not_BH; eauto.
Qed.

(* ------------------------------------------------------- *)
(* Lemmi "monotoni" condizionali                           *)
(* ------------------------------------------------------- *)
(* Questi lemmi sono intenzionalmente deboli: non
   assumono niente sui singoli witness JSON, ma danno
   frecce logiche riutilizzabili in v8 quando avremo
   vincoli più forti su meta_label.                        *)

Lemma SAFE_of_meta_label_0 :
  forall m, meta_label m = 0%Z -> is_SAFE m.
Proof.
  intros m H; unfold is_SAFE; auto.
Qed.

Lemma SAFE_of_meta_label_3 :
  forall m, meta_label m = 3%Z -> is_SAFE m.
Proof.
  intros m H; unfold is_SAFE; auto.
Qed.

Lemma BH_of_meta_label_9 :
  forall m, meta_label m = 9%Z -> is_BH m.
Proof.
  intros m H; unfold is_BH; auto.
Qed.

(* ------------------------------------------------------- *)
(* Fine file SAFE/BH                                       *)
(* ------------------------------------------------------- *)

