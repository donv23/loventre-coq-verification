(** Loventre_Phase_Assembly.v
    Integra SAFE + CLASS + RISK in una mappa di fasi.
    V77g — inversion per Rocq 9.1 + prove chiuse
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
  Loventre_Class_Properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(** ----------------------------------------------------------- **)
(** ASSIOMA: decidibilità locale di P-like                       **)
(** ----------------------------------------------------------- **)

Axiom dec_P_Lov :
  forall x : M, {In_P_Lov x} + {~ In_P_Lov x}.

(** ----------------------------------------------------------- **)
(** DEFINIZIONE DI FASE                                          **)
(** ----------------------------------------------------------- **)

Inductive Loventre_Phase :=
| PHASE_GREEN
| PHASE_YELLOW
| PHASE_BLACKHOLE.

(** ----------------------------------------------------------- **)
(** FUNZIONE DI ASSEMBLAGGIO — fuel-aware                        **)
(** ----------------------------------------------------------- **)

Definition classify_phase (x : M) : Loventre_Phase :=
  let f := classify_risk (S O) in
  let r := f x in
  match r with
  | RISK_LOW =>
      match dec_P_Lov x with
      | left _ => PHASE_GREEN
      | right _ => PHASE_YELLOW
      end
  | RISK_MEDIUM =>
      PHASE_YELLOW
  | RISK_HIGH =>
      PHASE_BLACKHOLE
  end.

(** ----------------------------------------------------------- **)
(** PROPRIETÀ MINIME                                             **)
(** ----------------------------------------------------------- **)

Lemma phase_green_means_not_blackhole :
  forall x, classify_phase x = PHASE_GREEN -> ~ In_NPbh_Lov x.
Proof.
  unfold classify_phase.
  intros x H.
  remember (classify_risk (S O) x) as r eqn:Hr.
  destruct r; try inversion H.
  destruct (dec_P_Lov x); intros; subst; try inversion H.
  apply P_exclusive_NPbh; assumption.
Qed.

Lemma blackhole_phase_ge_risk_high :
  forall x, classify_phase x = PHASE_BLACKHOLE ->
            classify_risk (S O) x = RISK_HIGH.
Proof.
  unfold classify_phase.
  intros x H.
  remember (classify_risk (S O) x) as r eqn:Hr.
  destruct r.
  - now inversion H.
  - now inversion H.
  - exact Hr.
Qed.

