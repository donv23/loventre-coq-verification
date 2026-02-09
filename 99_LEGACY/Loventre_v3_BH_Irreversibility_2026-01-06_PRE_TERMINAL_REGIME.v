From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_v3_LClass.
Require Import Loventre_v3_Policy.
Require Import Loventre_v3_Curvature.
Require Import Loventre_v3_DeltaCurvature.
Require Import Loventre_v3_DynamicPolicy.

(* =================================================== *)
(* Loventre v3 — Irreversibilità geometrica di P_BH     *)
(* =================================================== *)

(* In v3, delta_kappa è direzionale:
   δ(c1,c2) = κ(c2) - κ(c1)
   quindi se c2 ha curvatura minore, δ=0

   Questo implica:
   - P_BH→P_BH  : δ=0 → GREEN
   - P_BH→P_ACC : δ=0 → GREEN
   - P_BH→P_STR : δ=0 → GREEN
*)

Lemma Loventre_v3_BH_self :
  Loventre_v3_dynamic_policy P_BH P_BH = L_GREEN.
Proof.
  unfold Loventre_v3_dynamic_policy.
  simpl.
  reflexivity.
Qed.

Lemma Loventre_v3_BH_to_ACC :
  Loventre_v3_dynamic_policy P_BH P_ACC = L_GREEN.
Proof.
  unfold Loventre_v3_dynamic_policy.
  simpl.
  reflexivity.
Qed.

Lemma Loventre_v3_BH_to_STR :
  Loventre_v3_dynamic_policy P_BH P_STR = L_GREEN.
Proof.
  unfold Loventre_v3_dynamic_policy.
  simpl.
  reflexivity.
Qed.

