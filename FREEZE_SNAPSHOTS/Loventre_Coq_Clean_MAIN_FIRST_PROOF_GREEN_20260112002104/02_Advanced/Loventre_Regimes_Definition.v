(******************************************************)
(* Loventre_Regimes_Definition — V50 Coq-clean        *)
(* Fully namespaced Advanced → Core imports           *)
(******************************************************)

From Loventre_Core Require Import Loventre_Kernel.
From Loventre_Core Require Import Loventre_Foundation_Types.
From Loventre_Core Require Import Loventre_Foundation_Time.
From Loventre_Core Require Import Loventre_Foundation_Params.
From Loventre_Core Require Import Loventre_Foundation_Entropy.
From Loventre_Core Require Import Loventre_Foundation_Logic.
From Loventre_Core Require Import Loventre_Foundation_Measures.

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
Open Scope R_scope.

(******************************************************)
(* Loventre regime classification baseline structure  *)
(******************************************************)

Inductive regime_level :=
| regime_low
| regime_mid
| regime_critical.

Record loventre_regime_summary := {
  regime_kappa : R;
  regime_entropy : R;
  regime_mass : R;
  regime_level_flag : regime_level
}.

(******************************************************)
(* Decision function — midpoint threshold prototype   *)
(******************************************************)

Definition baseline_threshold (k e : R) : R :=
  (k + e) / 2.

Definition classify_regime (rs : loventre_regime_summary) : regime_level :=
  if Rle_dec rs.(regime_entropy) (baseline_threshold rs.(regime_kappa) rs.(regime_entropy))
  then regime_low
  else if Rle_dec rs.(regime_entropy) rs.(regime_kappa)
       then regime_mid
       else regime_critical.

(******************************************************)
(* Sanity lemma — if entropy small, classification OK *)
(******************************************************)

Lemma classify_regime_low :
  forall rs,
    rs.(regime_entropy) <= baseline_threshold rs.(regime_kappa) rs.(regime_entropy) ->
    classify_regime rs = regime_low.
Proof.
  intros rs H.
  unfold classify_regime, baseline_threshold in *.
  destruct (Rle_dec (regime_entropy rs)
                    ((regime_kappa rs + regime_entropy rs) / 2)).
  - reflexivity.
  - exfalso; apply n; exact H.
Qed.

Close Scope R_scope.

