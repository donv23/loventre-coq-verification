(*
   Loventre_LMetrics_Time_Simulate_v700.v
   Evoluzione iterata delle metriche nel tempo (basata su v690)
*)

From Loventre_Core       Require Import Loventre_Core_Prelude.
From Loventre_Advanced   Require Import Loventre_LMetrics_Core
                                Loventre_Metrics_Bus.
From Loventre_Advanced.Geometry
                         Require Import Loventre_LMetrics_Structure.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

(* === JSON BASE PATH === *)
Definition base_path : string :=
  "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/".

Definition file_P_like    := string_append base_path "metrics_P_like_v690.json".
Definition file_Pacc      := string_append base_path "metrics_Pacc_v690.json".
Definition file_3SATcrit  := string_append base_path "metrics_3SATcrit_v690.json".

(* === Loader === *)
Definition load_lmetrics (fname : string) : option LMetrics :=
  load_json_LMetrics fname.

Definition l_init : option LMetrics :=
  load_lmetrics file_P_like.

(* === Evoluzione elementare (passo singolo) === *)
Definition evolve_once (m : LMetrics) : LMetrics :=
  {| kappa_eff      := kappa_eff m + 0.1 ;
     entropy_eff    := entropy_eff m + 0.05 ;
     V0             := V0 m + 0.08 ;
     a_min         := a_min m + 0.01 ;
     p_tunnel      := p_tunnel m * 1.02 ;
     P_success     := P_success m * 0.98 ;
     gamma_dilation := gamma_dilation m + 0.02 ;
     time_regime    := time_regime m ;
     mass_eff       := mass_eff m + 0.03 ;
     inertial_idx   := inertial_idx m + 0.01 ;
     risk_index     := risk_index m + 0.02 ;
     chi_compactness := chi_compactness m + 0.01 ;
     horizon_flag   := horizon_flag m
  |}.

(* === Evoluzione multipla === *)
Fixpoint evolve_n (m : LMetrics) (n : nat) : LMetrics :=
  match n with
  | O => m
  | S k => evolve_once (evolve_n m k)
  end.

(* === Lista di timeline: [L0; L1; L2; ...; LN] === *)
Fixpoint simulate (m : LMetrics) (n : nat) : list LMetrics :=
  match n with
  | O => [m]
  | S k => m :: simulate (evolve_once m) k
  end.

(* === Lemmi di sanity === *)

Lemma evolve_entropy_non_decreasing :
  forall m, entropy_eff m <= entropy_eff (evolve_once m).
Proof. intros; unfold evolve_once; lra. Qed.

Lemma evolve_barrier_increasing :
  forall m, V0 m < V0 (evolve_once m).
Proof. intros; unfold evolve_once; lra. Qed.

Lemma evolve_chain_len :
  forall m n, length (simulate m n) = S n.
Proof.
  induction n; simpl; auto.
Qed.

(* === Theorem: la timeline esiste per N passi se l0 carica === *)
Theorem v700_simulation_valid :
  forall n, exists lst,
    l_init = Some (hd (default_lmetrics) lst) /\
    length lst = S n.
Proof.
  intros n.
  destruct l_init eqn:E.
  - exists (simulate l n). split; auto.
    simpl. reflexivity || auto.
  - exists []. split; auto.
Qed.

