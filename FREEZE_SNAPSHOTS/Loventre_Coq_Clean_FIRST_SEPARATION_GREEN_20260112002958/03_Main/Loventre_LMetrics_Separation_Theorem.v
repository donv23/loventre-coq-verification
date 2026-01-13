(* Loventre_LMetrics_Separation_Theorem

   First explicit Loventre-style separation theorem (seed version):

     - we assume an abstract PolicyContract on the engine behaviour;

     - we define NP_like_crit_profile as the SAT/TSP-critical cone
       [Metrics_witness];

     - we prove a structural separation:

           no NP_like-critical state can be globally SAFE.

   We then specialise this to the JSON witnesses TSPcrit28/SATcrit16.
*)

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_SAT_TSP_Critical_Metrics
  Loventre_LMetrics_Witness_CLI
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Instances
  Loventre_LMetrics_Policy_Axioms.

Module MB     := Loventre_Metrics_Bus.
Module Crit   := Loventre_SAT_TSP_Critical_Metrics.
Module CLI    := Loventre_LMetrics_Witness_CLI.
Module JSONW  := Loventre_LMetrics_JSON_Witness.
Module Inst   := Loventre_LMetrics_Instances.
Module Policy := PolicyAxioms.

Import MB.

Definition LMetrics : Type := MB.LMetrics.
Definition BusState : Type := Crit.BusState.

(* NP_like-critical profile: by definition, the SAT/TSP-critical cone. *)
Definition NP_like_crit_profile (m : LMetrics) : Prop :=
  Crit.Metrics_witness m.

Section SeparationUnderPolicyContract.

  (* Global hypothesis: the engine satisfies the Policy contract. *)
  Variable Hpolicy : Policy.PolicyContract.

  (* Separation theorem:

       If [m] is NP_like-critical (i.e. inside [Metrics_witness]),
       then it cannot have SAFE global decision.
   *)
  Theorem Loventre_separation :
    forall m : LMetrics,
      NP_like_crit_profile m ->
      loventre_global_decision m <> GD_safe.
  Proof.
    intros m Hnp Hsafe.
    unfold NP_like_crit_profile in Hnp.
    (* From the contract: a witness is always BORDERLINE or CRITICAL. *)
    pose proof (Policy.policy_witnesses_borderline_or_critical Hpolicy m Hnp)
      as Hcases.
    destruct Hcases as [Hborder | Hcrit].
    - rewrite Hborder in Hsafe. discriminate.
    - rewrite Hcrit in Hsafe. discriminate.
  Qed.

  (* JSON witnesses are NP_like-critical by contract. *)

  Lemma m_TSPcrit28_json_is_NP_like_crit :
    NP_like_crit_profile JSONW.m_TSPcrit28_json.
  Proof.
    unfold NP_like_crit_profile.
    apply (Policy.policy_TSPcrit28_json_is_TSP_crit Hpolicy).
  Qed.

  Lemma m_SATcrit16_json_is_NP_like_crit :
    NP_like_crit_profile JSONW.m_SATcrit16_json.
  Proof.
    unfold NP_like_crit_profile.
    apply (Policy.policy_SATcrit16_json_is_SAT_crit Hpolicy).
  Qed.

  (* Concrete corollaries: JSON NP_like-critical witnesses
     cannot be SAFE. *)

  Corollary TSPcrit28_json_not_safe :
    loventre_global_decision JSONW.m_TSPcrit28_json <> GD_safe.
  Proof.
    apply Loventre_separation.
    apply m_TSPcrit28_json_is_NP_like_crit.
  Qed.

  Corollary SATcrit16_json_not_safe :
    loventre_global_decision JSONW.m_SATcrit16_json <> GD_safe.
  Proof.
    apply Loventre_separation.
    apply m_SATcrit16_json_is_NP_like_crit.
  Qed.

End SeparationUnderPolicyContract.

(* Tiny sanity goal so that [coqc] never sees an empty file. *)
Goal True. exact I. Qed.
