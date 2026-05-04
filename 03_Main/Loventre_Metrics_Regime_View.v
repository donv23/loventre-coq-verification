(** Loventre_Metrics_Regime_View.v
    Vista unificata dei regimi metrici (LMetrics) per SAT_crit e TSP_crit.

    Scopo:
      - Definire un predicato is_collapse_regime che cattura esattamente
        la forma del collasso metrico usata in:
          * Loventre_SAT_Critical_Collapse
          * Loventre_TSP_Critical_Collapse
      - Riesprimere tali collassi come teoremi "di vista", più leggibili.
      - Fornire un lemma congiunto che dice che, oltre una certa soglia n0,
        SAT_crit e TSP_crit sono simultaneamente in regime di collasso.
 *)

From Coq Require Import Arith Lia.

Require Import Loventre_Metrics_Bus.
Require Import Loventre_SAT_Critical_Metrics.
Require Import Loventre_TSP_Critical_Metrics.
Require Import Loventre_SAT_Critical_Collapse.
Require Import Loventre_TSP_Critical_Collapse.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_Metrics_Regime_View.

  Module MB     := Loventre_Metrics_Bus.Loventre_Metrics_Bus.
  Module SATMet := Loventre_SAT_Critical_Metrics.Loventre_SAT_Critical_Metrics.
  Module TSPMet := Loventre_TSP_Critical_Metrics.Loventre_TSP_Critical_Metrics.
  Module SATCol := Loventre_SAT_Critical_Collapse.Loventre_SAT_Critical_Collapse.
  Module TSPCol := Loventre_TSP_Critical_Collapse.Loventre_TSP_Critical_Collapse.

  (** Regime di "collasso critico" per una metrica LMetrics:
        - meta_label è NP_like_critico oppure NP_like_black_hole
        - global_decision è RITIRA
      Questo è esattamente lo schema usato dalle congetture di collasso.
   *)
  Definition is_collapse_regime (m : MB.LMetrics) : Prop :=
    (MB.meta_label m = MB.NP_like_critico \/
     MB.meta_label m = MB.NP_like_black_hole) /\
    MB.global_decision m = MB.RITIRA.

  (** Vista del collasso metrico SAT_crit in forma compatta. *)
  Theorem Loventre_SAT_crit_collapse_view :
    exists n0 : nat,
      forall n : nat,
        (n >= n0)%nat ->
          is_collapse_regime (SATMet.SAT_crit_metrics_family n).
  Proof.
    unfold is_collapse_regime.
    exact SATCol.Loventre_SAT_crit_metrics_collapse.
  Qed.

  (** Vista del collasso metrico TSP_crit in forma compatta. *)
  Theorem Loventre_TSP_crit_collapse_view :
    exists n0 : nat,
      forall n : nat,
        (n >= n0)%nat ->
          is_collapse_regime (TSPMet.TSP_crit_metrics_family n).
  Proof.
    unfold is_collapse_regime.
    exact TSPCol.Loventre_TSP_crit_metrics_collapse.
  Qed.

  (** Lemma congiunto:
        esiste una soglia n0 tale che, per ogni n >= n0,
        SAT_crit e TSP_crit sono contemporaneamente in regime di collasso
        sul Loventre Metrics Bus.
   *)
  Theorem Loventre_SAT_TSP_joint_collapse_regime :
    exists n0 : nat,
      forall n : nat,
        (n >= n0)%nat ->
          is_collapse_regime (SATMet.SAT_crit_metrics_family n) /\
          is_collapse_regime (TSPMet.TSP_crit_metrics_family n).
  Proof.
    destruct Loventre_SAT_crit_collapse_view as [n_sat Hsat].
    destruct Loventre_TSP_crit_collapse_view as [n_tsp Htsp].
    exists (Nat.max n_sat n_tsp).
    intros n Hge.
    split.
    - apply Hsat. lia.
    - apply Htsp. lia.
  Qed.

End Loventre_Metrics_Regime_View.

