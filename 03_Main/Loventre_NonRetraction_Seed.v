From Stdlib Require Import Reals.

Require Import 02_Advanced.Geometry.Loventre_Metrics_Bus.

Module Loventre_NonRetraction_Seed.

Module LM := Loventre_Metrics_Bus.

(* SAFE and BLACK *)
Definition is_safe (m : LM.LMetrics) : Prop :=
  m.(LM.horizon_flag) = false.

Definition is_black (m : LM.LMetrics) : Prop :=
  m.(LM.horizon_flag) = true.

(* NP-like accessible *)
Definition np_like_accessible (m : LM.LMetrics) : Prop :=
  is_black m /\ (m.(LM.entropy_eff) > m.(LM.kappa_eff)).

(* informational equivalence *)
Definition equivalent_metrics (m1 m2 : LM.LMetrics) : Prop :=
  (m1.(LM.horizon_flag) = m2.(LM.horizon_flag)) /\
  (m1.(LM.entropy_eff) = m2.(LM.entropy_eff)) /\
  (m1.(LM.kappa_eff)   = m2.(LM.kappa_eff)).

(* Non-retraction theorem seed *)
Theorem non_retraction :
  forall m_black,
       np_like_accessible m_black ->
       ~ (exists m_safe, is_safe m_safe /\ equivalent_metrics m_black m_safe).
Proof.
Admitted.

Corollary Loventre_Complexity_Separation :
  ~ (exists m, is_safe m /\ np_like_accessible m).
Proof.
Admitted.

End Loventre_NonRetraction_Seed.

