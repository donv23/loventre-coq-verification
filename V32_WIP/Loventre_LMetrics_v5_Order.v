(**
  Loventre_LMetrics_v5_Order.v
  -----------------------------
  Ordine totale lessicografico su LMetric
  Compatibile con Coq 9 / Stdlib.
*)

From Stdlib Require Import Reals Raxioms Rbase Psatz.
From Stdlib Require Import List.
Import ListNotations.

Open Scope R_scope.

(** ========================================================================= *)
(** Definizione astratta di LMetric per l'ordine *)
(** ========================================================================= *)

Record LMetric := {
  kappa_eff       : R;
  entropy_eff     : R;
  V0              : R;
  p_tunnel        : R;
  P_success       : R
}.

(** ========================================================================= *)
(** Converte la struttura in una tupla di confronto *)
(** ========================================================================= *)

Definition lm_tuple (m : LMetric) : list R :=
  [ m.(kappa_eff) ;
    m.(entropy_eff) ;
    m.(V0) ;
    m.(p_tunnel) ;
    m.(P_success) ].

(** ========================================================================= *)
(** Ordine lessicografico per liste di reali                         *)
(** ========================================================================= *)

Fixpoint lexR (xs ys : list R) : Prop :=
  match xs, ys with
  | [], [] => True
  | x::xs', y::ys' =>
      (x < y) \/ (x = y /\ lexR xs' ys')
  | _, _ => False
  end.

Definition lm_le (m1 m2 : LMetric) : Prop :=
  lexR (lm_tuple m1) (lm_tuple m2).

(** ========================================================================= *)
(** Proprietà basilari *)
(** ========================================================================= *)

Lemma lexR_refl : forall xs, lexR xs xs.
Proof.
  induction xs; simpl; auto.
  right; split; auto.
Qed.

Lemma lm_le_refl : forall m, lm_le m m.
Proof.
  intro; unfold lm_le; apply lexR_refl.
Qed.

Lemma lexR_trans :
  forall xs ys zs,
    lexR xs ys -> lexR ys zs -> lexR xs zs.
Proof.
  induction xs; destruct ys; destruct zs; simpl; intros; try tauto.
  destruct H as [Hlt|[Heq Hrest]].
  - destruct H0 as [Hlt'|[Heq' _]]; try lra; left; lra.
  - destruct H0 as [Hlt'|[Heq' Hrest']].
    + left; subst; lra.
    + right; split; subst; auto.
Qed.

Lemma lm_le_trans :
  forall m1 m2 m3,
    lm_le m1 m2 -> lm_le m2 m3 -> lm_le m1 m3.
Proof.
  unfold lm_le; intros; eapply lexR_trans; eauto.
Qed.

Lemma lexR_total :
  forall xs ys, lexR xs ys \/ lexR ys xs.
Proof.
  induction xs; destruct ys; simpl; try tauto.
  destruct (Rlt_dec a r) as [Hlt|Hnlt].
  - left; left; exact Hlt.
  - destruct (Rlt_dec r a) as [Hgt|Hnge].
    + right; left; exact Hgt.
    + assert (a = r) by lra; subst.
      destruct (IHxs ys) as [H|H].
      * left; right; split; auto.
      * right; right; split; auto.
Qed.

Lemma lm_le_total :
  forall m1 m2, lm_le m1 m2 \/ lm_le m2 m1.
Proof.
  unfold lm_le; intros; apply lexR_total.
Qed.

Theorem lm_le_is_total_order :
  forall m1 m2, lm_le m1 m2 \/ lm_le m2 m1.
Proof.
  apply lm_le_total.
Qed.

