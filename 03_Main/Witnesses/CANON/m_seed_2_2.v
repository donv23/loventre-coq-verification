From Stdlib Require Import Reals.
From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Structure.

Open Scope R_scope.

Definition m_seed_2_2 : LMetrics :=
{|
  kappa_eff := 2.0;
  entropy_eff := 2.0;
  V0 := 4.0;
  p_tunnel := 0.2;
  P_success := 0.6;
  barrier_tag := 0.0;
  informational_potential := 0.0
|}.

