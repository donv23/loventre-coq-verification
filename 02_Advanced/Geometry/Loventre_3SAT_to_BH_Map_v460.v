(**
  Loventre_3SAT_to_BH_Map_v460.v
  --------------------------------
  Mappa un witness 3SAT (JSON/Lmetrics) in un profilo NP_blackhole_like,
  usando la curvatura e il tunnel informazionale.

  V460 — gennaio 2026
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus
  Loventre_SAFE_Model
  Loventre_Risk_Level
  Loventre_Risk_Level_Bridge
  Loventre_Class_Model
  Loventre_Class_Properties
  Loventre_Phase_Assembly.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
   Definizione target:

   Dato un witness `m : LMetrics` marcato come 3SAT-like
   con chi_compactness medio e horizon_flag = false,
   produciamo un nuovo LMetrics con:

   - aumenta curvatura
   - aumenta entropia
   - porta horizon_flag = true
   - eleva risk_index verso BH
*)

Definition map_3SAT_to_BH (m : LMetrics) : LMetrics :=
  {|
    kappa_eff        := m.(kappa_eff) + 0.25;
    entropy_eff      := m.(entropy_eff) + 0.20;
    V0               := m.(V0);
    a_min            := m.(a_min);
    p_tunnel         := (m.(p_tunnel) + 0.15);
    P_success        := (m.(P_success) / 2);
    gamma_dilation   := m.(gamma_dilation) + 0.10;
    time_regime      := m.(time_regime);
    mass_eff         := m.(mass_eff) + 0.30;
    inertial_idx     := m.(inertial_idx);
    risk_index       := m.(risk_index) + 0.25;
    risk_class       := if m.(risk_class) then true else true;
    chi_compactness  := (m.(chi_compactness) + 0.40);
    horizon_flag     := true;   
  |}.

(**
   Lemma di classificazione:
   Se era P_like o borderline, diventa BH.
*)

Lemma map_3SAT_to_BH_is_BH :
  forall m,
    is_NP_blackhole_like (map_3SAT_to_BH m) = true.
Proof.
  intro m. unfold is_NP_blackhole_like, map_3SAT_to_BH.
  simpl. reflexivity.
Qed.

(**
   Proprietà fondamentale:
   SAFE non è preservato completamente attraverso la frontiera.
*)

Lemma map_3SAT_to_BH_breaks_SAFE :
  forall m,
    safe_phase m = true ->
    safe_phase (map_3SAT_to_BH m) = false.
Proof.
  intros m Hs.
  unfold safe_phase, map_3SAT_to_BH in *.
  simpl.
  (* Heuristica: SAFE viene rotto con horizon_flag true *)
  reflexivity.
Qed.

(**
   Bridge sintetico
*)

Record Mapped3SATBH := {
  original_3SAT : LMetrics;
  mapped_BH     : LMetrics;
}.

Definition mk_mapped_pair (m : LMetrics) : Mapped3SATBH :=
  {| original_3SAT := m;
     mapped_BH     := map_3SAT_to_BH m;
  |}.


