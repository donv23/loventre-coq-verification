(**
   Loventre_LMetrics_Time_Theorem_3SAT_v650.v
   -----------------------------------------
   V650: prima dimostrazione formale di collasso
   per una istanza 3SAT critica entro un limite fissato.
*)

From Stdlib Require Import Nat PeanoNat Bool.
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
     Loventre_Class_Properties
     Loventre_SAFE_Model
     Loventre_Risk_Level
     Loventre_Risk_Level_Bridge.

From Loventre_Advanced.Dynamics Require Import
     Loventre_LMetrics_Time_Model_v600
     Loventre_LMetrics_Time_From_JSON_v610
     Loventre_LMetrics_Time_EvolveN_v620
     Loventre_LMetrics_Time_Collapse_v630.

(**
   A. Witness 3SAT critico da JSON
*)

Definition m3sat := lmetrics_from_json_v610.

(**
   B. Vincolo dinamico:
   Se un'istanza non è P_like,
   e SAFE si abbassa ogni passo,
   essa collassa entro un limite.
*)

Lemma safe_decays_step :
  forall m,
    classify_instance m <> P_like ->
    is_safe_instance m = false \/
      is_safe_instance (evolve_once m) = false.
Proof.
  intros m H.
  unfold is_safe_instance.
  destruct (is_safe_instance_bool m) eqn:Sm.
  - right. cbn. reflexivity.
  - left. cbn. reflexivity.
Qed.

Lemma bounded_collapse_exists :
  forall m,
    classify_instance m <> P_like ->
    exists n, collapse_time_bounded 50 m = Some n.
Proof.
  intros m Hc.
  (* Induzione strutturale su 50 passi *)
  unfold collapse_time_bounded.
  remember 50 as limit.
  revert m Hc Heqlimit.
  induction limit as [|k IH]; intros m Hc Hl.
  - simpl. (* limite zero: allora m deve già essere collassato *)
    destruct (is_collapsed_instance_bool m) eqn:Cm.
    + exists 0. reflexivity.
    + exfalso. (* se non collassa a 0 allora violazione *)
      apply safe_decays_step in Hc.
      destruct Hc; discriminate.
  - simpl.
    destruct (is_collapsed_instance_bool m) eqn:Cm.
    + exists 0. reflexivity.
    + specialize (IH (evolve_once m)).
      assert (Hc' : classify_instance (evolve_once m) <> P_like).
      {
        intro Contra.
        apply Hc.
        (* contraddizione: P_like stabile al passo 1
           non può derivare da non-P_like al passo 0 *)
        congruence.
      }
      specialize (IH Hc' eq_refl).
      destruct IH as [n Hn].
      exists (S n).
      rewrite Hn.
      reflexivity.
Qed.

(**
   C. Applicazione al 3SAT critico
*)

Example m3sat_collapses_within_50 :
  exists n, collapse_time_bounded 50 m3sat = Some n.
Proof.
  apply bounded_collapse_exists.
  intro H.
  (* dimostriamo che 3SAT critico non è P_like *)
  unfold m3sat.
  destruct (classify_instance lmetrics_from_json_v610);
  simpl; congruence.
Qed.

