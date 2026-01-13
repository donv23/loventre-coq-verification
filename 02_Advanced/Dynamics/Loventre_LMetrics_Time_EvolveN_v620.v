(**
   Loventre_LMetrics_Time_EvolveN_v620.v
   -------------------------------------
   Estende V600 e V610 introducendo evoluzione iterata.
   Obiettivo:
   - iterare evolve_once N volte
   - restituire tempo finale + metrica finale
*)

From Stdlib Require Import Nat PeanoNat.
From Loventre_Core Require Import
     Loventre_Core_Prelude
     Loventre_Kernel
     Loventre_Foundation_Types
     Loventre_Foundation_Params
     Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_Metrics_Bus
     Loventre_Curvature_Field
     Loventre_Potential_Field
     Loventre_Barrier_Model
     Loventre_Risk_Level
     Loventre_Tunneling_Model
     Loventre_Class_Properties
     Loventre_LMetrics_JSON_Witness.

From Loventre_Advanced.Dynamics Require Import
     Loventre_LMetrics_Time_Model_v600
     Loventre_LMetrics_Time_From_JSON_v610.

Set Primitive Projections.

(**
   A. Evoluzione iterata: definizione ricorsiva pura
*)

Fixpoint evolve_n (n : nat) (m : LMetrics_Time) : LMetrics_Time :=
  match n with
  | O => m
  | S n' => evolve_n n' (evolve_once m)
  end.

(**
   B. Pipeline: LMetrics → evolve_n → LMetrics
*)

Definition metrics_after_n_steps (n : nat) (m : LMetrics) : LMetrics :=
  let t0 := time_init_from_metrics m in
  lm_now (evolve_n n t0).

(**
   C. Due proprietà base a garanzia del modello dinamico
*)

Lemma evolve_n_zero :
  forall m, evolve_n 0 m = m.
Proof. reflexivity. Qed.

Lemma evolve_n_tick_accumulates :
  forall n m,
    lm_tick (evolve_n n m) = lm_tick m + n.
Proof.
  induction n as [|n IH]; intros m.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

(**
   D. Proprietà compositiva:
      n + k evoluzioni equivalgono a fare n e poi k
*)

Lemma evolve_n_compose :
  forall n k m,
    evolve_n (n + k) m = evolve_n k (evolve_n n m).
Proof.
  induction n as [|n IH]; intros k m.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

