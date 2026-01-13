(**
 * Loventre_LMetrics_Time_Select_v710.v
 * Versione 710 - Dinamica deterministica per selezione di stato
 *)

From Stdlib Require Import List Arith Bool.

From Loventre_Core Require Import
  Loventre_Core_Prelude
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus
  Loventre_Class_Model
  Loventre_Phase_Assembly
  Loventre_SAFE_Model
  Loventre_Risk_Level
  Loventre_Risk_Level_Bridge.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure.

(**
  Regola V710:
  - Se risk_index < 30     ⇒ rimani P_like
  - Se 30 ≤ risk_index <60 ⇒ passa a P_accessible
  - Se ≥ 60                ⇒ NP_like_black_hole (3SAT_critico)
 *)

Definition evolve_select_v710 (m : LMetrics) : LMetrics :=
  let r := risk_index m in
  if r <? 30 then
      (* Rimane P_like *)
      m
  else if r <? 60 then
      (* Promozione a P_accessible *)
      {| kappa_eff := kappa_eff m ;
         entropy_eff := entropy_eff m ;
         V0 := V0 m ;
         a_min := a_min m ;
         p_tunnel := p_tunnel m ;
         P_success := P_success m ;
         gamma_dilation := gamma_dilation m ;
         time_regime := time_regime m ;
         mass_eff := mass_eff m ;
         inertial_idx := inertial_idx m ;
         risk_index := r ;
         risk_class := P_ClassAccessible ;
         chi_compactness := chi_compactness m ;
         horizon_flag := false
      |}
  else
      (* Collasso verso 3SATcritico / NPbh *)
      {| kappa_eff := kappa_eff m ;
         entropy_eff := entropy_eff m ;
         V0 := V0 m ;
         a_min := a_min m ;
         p_tunnel := p_tunnel m ;
         P_success := P_success m ;
         gamma_dilation := gamma_dilation m ;
         time_regime := time_regime m ;
         mass_eff := mass_eff m ;
         inertial_idx := inertial_idx m ;
         risk_index := r ;
         risk_class := NP_ClassBlackHole ;
         chi_compactness := chi_compactness m ;
         horizon_flag := true
      |}.

(**
  Lemma: evolve_select_v710 NON modifica valori fisici
 *)
Lemma evolve_v710_preserves_physical :
  forall m, 
    kappa_eff (evolve_select_v710 m) = kappa_eff m /\
    entropy_eff (evolve_select_v710 m) = entropy_eff m /\
    V0 (evolve_select_v710 m) = V0 m.
Proof.
  intros m.
  unfold evolve_select_v710.
  destruct (risk_index m <? 30) eqn:H1;
  try (repeat split; reflexivity).
  destruct (risk_index m <? 60) eqn:H2;
  repeat split; reflexivity.
Qed.

(**
  Lemma: se rischio ≥ 60, si entra in zona black-hole
 *)
Lemma evolve_v710_bh_threshold :
  forall m,
    risk_index m >= 60 ->
    horizon_flag (evolve_select_v710 m) = true.
Proof.
  intros m H.
  unfold evolve_select_v710.
  destruct (risk_index m <? 30) eqn:H1;
  [ apply Nat.ltb_lt in H1; lia |].
  destruct (risk_index m <? 60) eqn:H2;
  [ apply Nat.ltb_lt in H2; lia | reflexivity ].
Qed.

