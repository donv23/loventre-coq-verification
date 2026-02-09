(* ========================================================= *)
(* LOVENTRE ENGINE v7 — LMetrics Record Definition           *)
(* ========================================================= *)

From LMetrics_v7 Require Import LMetrics_v7_Prelude.

Record LMetricsV7 := {
   kappa_eff : Z;
   entropy_eff : Z;
   mass_eff : Z;
   inertial_idx : Z;
   risk_index : Z;
   meta_label : Z
}.

(* End of file *)

