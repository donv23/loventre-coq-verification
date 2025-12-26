(* Loventre_Metrics_Bus.v — definizione del bus delle metriche *)

From Stdlib Require Import Reals.

Record LMetrics := mkLM
{
kappa_eff : R;
entropy_eff : R;
V0 : R
}.

(* accessor canonici e stabili *)
Definition get_kappa (w : LMetrics) := kappa_eff w.
Definition get_entropy (w : LMetrics) := entropy_eff w.
Definition get_V0 (w : LMetrics) := V0 w.

(* esempio minimale *)
Definition zeroLM : LMetrics := mkLM 0 0 0.

Lemma lm_ok : True.
Proof. exact I. Qed.

