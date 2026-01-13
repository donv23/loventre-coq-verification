(**
 * Loventre_LMetrics_Time_NoReturn_v750.v
 * Versione 750 — Punto di Non Ritorno Informazionale
 *)

From Stdlib Require Import List Arith Bool Lia.

From Loventre_Core Require Import
  Loventre_Core_Prelude
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus
  Loventre_Class_Model
  Loventre_Phase_Assembly
  Loventre_SAFE_Model
  Loventre_Risk_Level
  Loventre_Risk_Level_Bridge.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure.

(**
  Definizione della soglia di non ritorno
  (numero astratto, coerente con risk_priority e collapse v630)
*)
Definition NO_RETURN_THRESHOLD : nat := 1.

(** Se il rischio supera la soglia → nessun ritorno possibile *)
Definition no_return_state (m : LMetrics) : Prop :=
  risk_index m >= NO_RETURN_THRESHOLD.

(**
  Lemma principale:
  se un'istanza è oltre soglia → evolve_once la porta inevitabilmente
  nello stato NP_ClassBlackHole.
*)
Lemma evolve_once_no_return_v750 :
  forall m,
    no_return_state m ->
    risk_class (evolve_once m) = NP_ClassBlackHole.
Proof.
  intros m H.
  unfold evolve_once.
  destruct (risk_class m) eqn:Hc.
  - (* P_ClassLike *)
    simpl in H.
    lia.
  - (* P_ClassAccessible *)
    simpl in H.
    lia.
  - (* NP_ClassBlackHole *)
    reflexivity.
Qed.

(** Corollario: oltre la soglia → non puoi tornare in P o Pacc *)
Lemma no_return_excludes_recovery :
  forall m,
    no_return_state m ->
      risk_class (evolve_once m) <> P_ClassLike
      /\ risk_class (evolve_once m) <> P_ClassAccessible.
Proof.
  intros m H.
  rewrite evolve_once_no_return_v750 by exact H.
  split; discriminate.
Qed.


