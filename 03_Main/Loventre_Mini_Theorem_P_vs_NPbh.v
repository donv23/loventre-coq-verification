(** Loventre_Mini_Theorem_P_vs_NPbh.v
    Primo mini-teorema formale:
    Nessuna istanza P-like può essere NP-black-hole
    (nel modello Loventre, nel senso delle classi definite).
 *)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Params.

From Loventre_Advanced Require Import
  Loventre_Tunneling_Model
  Loventre_Barrier_Model
  Loventre_Risk_Level
  Loventre_SAFE_Model
  Loventre_Class_Model
  Loventre_Risk_Level_Bridge
  Loventre_Class_Properties
  Loventre_Phase_Assembly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(** ----------------------------------------------------------- **)
(** TEOREMA MINI - CORE STATEMENT                               **)
(** ----------------------------------------------------------- **)

Theorem loventre_P_never_NPbh :
  forall x : M,
    In_P_Lov x ->
    ~ In_NPbh_Lov x.
Proof.
  intro x; intro Hpx.
  (* versione aggiornata: il lemma ora si chiama P_exclusive_NPbh *)
  apply P_exclusive_NPbh.
  exact Hpx.
Qed.

(** ----------------------------------------------------------- **)
(** COROLLARIO DERIVATO                                         **)
(** ----------------------------------------------------------- **)

Corollary loventre_green_phase_never_bh :
  forall x,
    classify_phase x = PHASE_GREEN ->
    ~ In_NPbh_Lov x.
Proof.
  intros x Hgreen.
  apply phase_green_means_not_blackhole.
  exact Hgreen.
Qed.

