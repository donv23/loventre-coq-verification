(**
  Loventre_LMetrics_Time_Exact_v660.v
  Versione 660 — definizione del tempo di collasso esatto
  Introduce: 
    • funzione di tempo minimo
    • lemma di monotonia
    • lemma di minimalità
    • applicazione a m3sat_critico
*)

From Stdlib Require Import Arith.
From Loventre_Core Require Import
  Loventre_Core_Prelude
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
  Loventre_Curvature_Field
  Loventre_Potential_Field
  Loventre_Barrier_Model
  Loventre_Tunneling_Model
  Loventre_Risk_From_Tunneling
  Loventre_Risk_Level
  Loventre_Risk_Level_Bridge
  Loventre_SAFE_Model
  Loventre_Class_Model
  Loventre_Class_Properties
  Loventre_Phase_Assembly
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus.

From Loventre_Advanced.Geometry Require Import
  Loventre_Formal_Core
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure
  Loventre_LMetrics_JSON_Witness.

(**
  Pre-requisito:
  Abbiamo m3sat_crit come witness JSON validato.
*)

Definition evolve_step (m : LMetrics) : LMetrics :=
  evolve_once m.

Fixpoint evolve_n (n : nat) (m : LMetrics) : LMetrics :=
  match n with
  | 0 => m
  | S k => evolve_n k (evolve_step m)
  end.

(** Predicato: m è collassato verso NP_blackhole *)
Definition collapsed (m : LMetrics) : Prop :=
  is_NP_blackhole m = true.

(**
  Funzione parziale: se collassa entro LIMIT allora Some k,
  altrimenti None.
*)
Fixpoint collapse_time_bounded (LIMIT : nat) (m : LMetrics) : option nat :=
  match LIMIT with
  | 0 => if collapsed m then Some 0 else None
  | S k =>
      if collapsed m then Some 0
      else match collapse_time_bounded k (evolve_step m) with
           | Some n => Some (S n)
           | None => None
           end
  end.

(** Definizione di tempo esatto (minimo) *)
Definition collapse_time_exact (LIMIT : nat) (m : LMetrics) : option nat :=
  collapse_time_bounded LIMIT m.

(**
  Lemma 1 — Monotonia:
  Se m collassa entro LIMIT a passo n,
  allora evolve_n k m è collassato per ogni k ≥ n.
*)
Lemma collapse_monotone :
  forall m LIMIT n,
    collapse_time_bounded LIMIT m = Some n ->
    forall k,
      k >= n ->
      collapsed (evolve_n k m).
Proof.
  intros m LIMIT.
  induction LIMIT as [| LIMIT IH]; intros n H k Hge.
  - simpl in H.
    destruct (collapsed m) eqn:Hc; inversion H; subst.
    destruct k; simpl; try rewrite Hc; auto.
  - simpl in H.
    destruct (collapsed m) eqn:Hc.
    + inversion H; subst. clear H.
      destruct k.
      * simpl. rewrite Hc. auto.
      * simpl. rewrite Hc. auto.
    + destruct (collapse_time_bounded LIMIT (evolve_step m)) eqn:Hs; inversion H; subst.
      specialize (IH n Hs).
      destruct k.
      * simpl. auto.
      * simpl. apply IH. lia.
Qed.

(**
  Lemma 2 — Minimalità:
  Se il tempo di collasso è n,
  nessun j < n porta al collasso.
*)
Lemma collapse_minimal :
  forall m LIMIT n,
    collapse_time_bounded LIMIT m = Some n ->
    forall j,
      j < n ->
      collapsed (evolve_n j m) = false.
Proof.
  intros m LIMIT n H j Hlt.
  induction j as [|j IH] using lt_wf_ind.
  destruct j.
  - simpl.
    destruct (collapsed m) eqn:Hc; auto.
    assert (0 >= n) by lia.
    pose proof (collapse_monotone m LIMIT n H 0 H0).
    rewrite Hc in H1. discriminate.
  - simpl.
    specialize (IH j ltac:(lia)).
    destruct (collapsed (evolve_n (S j) m)) eqn:Hc.
    + destruct n.
      * inversion H.
      * assert (S j >= S n) by lia.
        pose proof (collapse_monotone m LIMIT (S n) H (S j) H0).
        simpl in H1. rewrite Hc in H1. discriminate.
    + auto.
Qed.

(** Applicazione al witness m3sat_crit *)
Definition m3sat := m3sat_crit.

Theorem m3sat_has_exact_collapse :
  exists n,
    collapse_time_exact 100 m3sat = Some n.
Proof.
  unfold collapse_time_exact.
  apply m3sat_crit_has_collapse.
Qed.

