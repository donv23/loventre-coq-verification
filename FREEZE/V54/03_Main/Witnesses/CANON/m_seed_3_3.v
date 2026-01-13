From Stdlib Require Import Reals.
From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Structure.

Open Scope R_scope.

Definition m_seed_3_3 : LMetrics :=
{|
  kappa_eff := 3.0;
  entropy_eff := 3.0;
  V0 := 9.0;
  p_tunnel := 0.1;
  P_success := 0.4;
  barrier_tag := 0.0;
  informational_potential := 0.0
|}.

