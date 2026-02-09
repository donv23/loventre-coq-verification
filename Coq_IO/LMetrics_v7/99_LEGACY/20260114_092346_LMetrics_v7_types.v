From Stdlib Require Import ZArith QArith String Lists.List.
Import ListNotations.

Open Scope Z_scope.
Open Scope Q_scope.

Record LMetrics_v7 := {
  vars_z : Z;
  clauses_z : Z;
  kappa_eff : Q;
  entropy_eff : Q;
  mass_eff : Q;
  inertial_idx : Q;
  risk_index : Q;
  meta_label : Z
}.

