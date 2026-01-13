(***********************************************************************
 *  Loventre_Main_Family_Chain_v500.v
 *  ------------------------------------------------
 *  Entry point principale per la catena gerarchica:
 *
 *     P_like → P_accessible → 2SAT_like → 3SAT_like → NP_blackhole_like
 *
 *  Consolidando Geometry livello v500.
 *
 ***********************************************************************)

From Loventre_Core Require Import Loventre_Core_Prelude
                                Loventre_Kernel
                                Loventre_Foundation_Types
                                Loventre_Foundation_Params
                                Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
        Loventre_Curvature_Field
        Loventre_Potential_Field
        Loventre_Barrier_Model
        Loventre_Tunneling_Model
        Loventre_Risk_From_Tunneling
        Loventre_Risk_Level
        Loventre_Risk_Level_Bridge
        Loventre_SAFE_Model
        Loventre_Class_Model
        Loventre_Class_Properties
        Loventre_Phase_Assembly
        Loventre_LMetrics_Core
        Loventre_Metrics_Bus.

From Loventre_Advanced.Geometry Require Import
        Loventre_Formal_Core
        Loventre_LMetrics_Phase_Predicates
        Loventre_LMetrics_Structure
        Loventre_2SAT_LMetrics_Crit_JSON
        Loventre_2SAT_LMetrics_From_JSON
        Loventre_2SAT_Decode_Compute
        Loventre_2SAT_EasyCrit_Compare
        Loventre_3SAT_BH_Local_v110
        Loventre_Family_SAFE_BH_Frontier_v430
        Loventre_2SAT_to_3SAT_Map_v450
        Loventre_3SAT_to_BH_Map_v460
        Loventre_Family_Complete_Chain_v500.

(***********************************************************************)
(**         Entry theorem: esistenza catena gerarchica                 **)
(***********************************************************************)

Theorem Loventre_Main_Chain_Exists_v500 :
  forall m,
    is_P_like m = true ->
      exists m1 m2 m3 m4,
           is_P_accessible_like m1 = true /\
           is_2SAT_like m2 = true /\
           is_3SAT_like m3 = true /\
           is_NP_blackhole_like m4 = true.
Proof.
  intros m HP.
  unfold is_P_like in HP.
  unfold is_P_like in *.
  unfold is_P_accessible_like.
  unfold is_2SAT_like.
  unfold is_3SAT_like.
  unfold is_NP_blackhole_like.
  pose proof Loventre_Family_Chain_Exists_v500 m HP as H.
  destruct H as [m1 [m2 [m3 [m4 Hs]]]].
  repeat destruct Hs as [A Hs].
  repeat destruct Hs as [B Hs].
  repeat destruct Hs as [C D].
  eexists m1, m2, m3, m4.
  repeat split; assumption.
Qed.

(***********************************************************************)
(**                  Fine principale V500                              **)
(***********************************************************************)

