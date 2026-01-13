content = """(* ******************************************************************* *)
(*                                                                     *)
(*   Test_Loventre_Theorem_v2_All.v                                    *)
(*                                                                     *)
(*   Driver di test globale per l'asse:                                *)
(*                                                                     *)
(*     - LMetrics Geometry (witness, fasi, Policy, SAFE, complessità); *)
(*     - Main (Policy Core Program, Theorem v1, v2_sketcḥ, v2_witness). *)
(*                                                                     *)
(*   Obiettivo: verificare che tutti i moduli chiave compilino         *)
(*   insieme sotto gli stessi prefissi logici.                         *)
(*                                                                     *)
(* ******************************************************************* *)

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus
  Loventre_SAT_TSP_Critical_Metrics
  Loventre_LMetrics_Witness_CLI
  Loventre_LMetrics_Witness_Lemmas
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Instances
  (* Loventre_LMetrics_SeedGrid_Lemmas (* usato altrove, non serve qui *) *)
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Policy_Spec
  Loventre_LMetrics_Policy_SAFE_Spec
  (* Loventre_LMetrics_Policy_Axioms (* caricato dove serve *) *)
  Loventre_LMetrics_Accessible_Existence
  Loventre_LMetrics_Complexity_Profiles
  Loventre_LMetrics_Complexity_Witness.

From Loventre_Main Require Import
  Loventre_LMetrics_First_Lemmas
  Loventre_LMetrics_Policy_Specs
  Loventre_LMetrics_Policy_Theorem
  Loventre_LMetrics_Separation_Program
  Loventre_Theorem_v1
  Loventre_Theorem_v1_Notes
  Loventre_Theorem_v2_Sketch
  Loventre_Theorem_v2_Witness.

Goal True. exact I. Qed.
"""

with open("Test_Loventre_Theorem_v2_All.v", "w", encoding="utf-8") as f:
    f.write(content)

print("Wrote Test_Loventre_Theorem_v2_All.v")

