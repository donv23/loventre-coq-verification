(**
 * Loventre_LMetrics_Time_Fusion_v720.v
 * Versione 720 - Fusione deterministica di dinamiche
 *)

From Stdlib Require Import List Arith Bool.

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
  Regola V720:
  Fusione tra due timeline LMetrics.

  Intuizione:
  - Si sceglie la parte più stabile dei due
  - P > Pacc > NPbh (in ordine di "bontà")
 *)

Definition class_priority (c : risk_class_type) : nat :=
  match c with
  | P_ClassLike => 0
  | P_ClassAccessible => 1
  | NP_ClassBlackHole => 2
  end.

Definition pick_best_class (c1 c2 : risk_class_type) : risk_class_type :=
  if Nat.ltb (class_priority c1) (class_priority c2)
  then c1 else c2.

Definition fuse_v720 (m1 m2 : LMetrics) : LMetrics :=
  let c := pick_best_class (risk_class m1) (risk_class m2) in
  let h :=
    match c with
    | NP_ClassBlackHole => true
    | _ => false
    end in
  {| kappa_eff := Nat.min (kappa_eff m1) (kappa_eff m2) ;
     entropy_eff := Nat.min (entropy_eff m1) (entropy_eff m2) ;
     V0 := Nat.min (V0 m1) (V0 m2) ;
     a_min := Nat.min (a_min m1) (a_min m2) ;
     p_tunnel := Nat.max (p_tunnel m1) (p_tunnel m2) ;
     P_success := Nat.min (P_success m1) (P_success m2) ;
     gamma_dilation := Nat.max (gamma_dilation m1) (gamma_dilation m2) ;
     time_regime := time_regime m1 ;
     mass_eff := mass_eff m1 ;
     inertial_idx := inertial_idx m1 ;
     risk_index := Nat.min (risk_index m1) (risk_index m2) ;
     risk_class := c ;
     chi_compactness := Nat.max (chi_compactness m1) (chi_compactness m2) ;
     horizon_flag := h
  |}.

(**
  Lemma 1: la fusione non peggiora la classe del migliore
 *)
Lemma fuse_v720_best_preserved :
  forall m1 m2,
    class_priority (risk_class (fuse_v720 m1 m2))
    = Nat.min (class_priority (risk_class m1))
              (class_priority (risk_class m2)).
Proof.
  intros m1 m2.
  unfold fuse_v720, pick_best_class.
  destruct (Nat.ltb (class_priority (risk_class m1))
                    (class_priority (risk_class m2))) eqn:H.
  - apply Nat.ltb_lt in H; reflexivity.
  - apply Nat.ltb_ge in H; reflexivity.
Qed.

