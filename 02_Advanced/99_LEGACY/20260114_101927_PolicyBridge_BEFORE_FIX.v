(* ====================================================== *)
(* LOVENTRE ENGINE v7 — LMetrics POLICY BRIDGE            *)
(* ====================================================== *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
  LMetrics_v7_Prelude
  LMetrics_v7_types
  LMetrics_v7_import
  LMetrics_v7_ProfileBridge.

(* Una policy banale:
   se kappa+entropy supera massa allora "1" (ok)
   altrimenti "0" (critico)
*)
Definition policy_decide (p : LMetricsV7_Profile) : Z :=
  if (Z.leb 0 (prof_kappa p + prof_entropy p - prof_mass p))
  then 1%Z else 0%Z.

(* Applichiamo la policy al primo witness *)
Definition policy_01 : Z :=
  policy_decide (to_profile witness_m_v7_3sat_DIMACS_01).

(* Lemma per verificare che la policy è definita *)
Lemma policy_decision_is_defined :
  policy_01 = 0%Z \/ policy_01 = 1%Z.
Proof.
  unfold policy_01, policy_decide.
  destruct (Z.leb_spec0 0 (prof_kappa (to_profile witness_m_v7_3sat_DIMACS_01) +
                           prof_entropy (to_profile witness_m_v7_3sat_DIMACS_01) -
                           prof_mass (to_profile witness_m_v7_3sat_DIMACS_01)));
  lia.
Qed.

