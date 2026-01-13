from pathlib import Path

content = r'''(* Loventre_LMetrics_Policy_Axioms

   Minimal policy contract for the Loventre Engine, focused on the
   SAT/TSP-critical cone and on a safe P-like seed.  This is the
   core needed to derive a first Loventre-style separation theorem
   in 03_Main.
*)

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_SAT_TSP_Critical_Metrics
  Loventre_LMetrics_Witness_CLI
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Instances.

Module PolicyAxioms.

  Module MB    := Loventre_Metrics_Bus.
  Module Crit  := Loventre_SAT_TSP_Critical_Metrics.
  Module CLI   := Loventre_LMetrics_Witness_CLI.
  Module JSONW := Loventre_LMetrics_JSON_Witness.
  Module Inst  := Loventre_LMetrics_Instances.

  Import MB.

  Definition LMetrics : Type := MB.LMetrics.
  Definition BusState : Type := Crit.BusState.

  (* PolicyContract: abstract package of assumptions about the
     qualitative behaviour of the engine on the metric bus. *)
  Record PolicyContract : Prop := {

    (* 1. SAT_crit / TSP_crit metrics are never globally SAFE:
          they are always BORDERLINE or CRITICAL. *)
    policy_witnesses_borderline_or_critical :
      forall (m : BusState),
        Crit.Metrics_witness m ->
          loventre_global_decision m = GD_borderline \/
          loventre_global_decision m = GD_critical;

    (* 2. The P-like seed [m_seed11_safe] is genuinely outside the
          SAT/TSP-critical cone: if it is SAFE, then it is not a
          SAT/TSP metric witness. *)
    policy_seed11_safe_not_metrics_witness :
      loventre_global_decision CLI.m_seed11_safe = GD_safe ->
      ~ Crit.Metrics_witness CLI.m_seed11_safe;

    (* 3. JSON witnesses are really inside the SAT/TSP-critical cone. *)
    policy_TSPcrit28_json_is_TSP_crit :
      Crit.TSP_crit JSONW.m_TSPcrit28_json;

    policy_SATcrit16_json_is_SAT_crit :
      Crit.SAT_crit JSONW.m_SATcrit16_json
  }.

End PolicyAxioms.
'''

Path("02_Advanced/Geometry/Loventre_LMetrics_Policy_Axioms.v").write_text(content, encoding="utf-8")
print("Wrote 02_Advanced/Geometry/Loventre_LMetrics_Policy_Axioms.v")

