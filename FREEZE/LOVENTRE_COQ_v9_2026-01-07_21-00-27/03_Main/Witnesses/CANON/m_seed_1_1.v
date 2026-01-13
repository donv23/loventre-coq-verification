From Stdlib Require Import Reals.
From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Structure.

Open Scope R_scope.

Definition m_seed_1_1 : LMetrics :=
{|
  kappa_eff := 1.0;
  entropy_eff := 1.0;
  V0 := 1.0;
  p_tunnel := 0.5;
  P_success := 1.0;
  barrier_tag := 0.0;
  informational_potential := 0.0
|}.

