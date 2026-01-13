(*
  Loventre_LMetrics_v7_Witness_From_JSON.v
  Witness V7 estratti da JSON (senza optional)
  Congelamento: Gennaio 2026
*)

From Stdlib Require Import Reals String.
Open Scope R_scope.

From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v7_Structure.
Import Loventre_LMetrics_V7_Structure.

(*
  Witness ridotto: contiene solo pochi campi minimi dal JSON.
  Niente optional, niente conversioni: qui tutto è già R/string/bool.
*)
Record LM_Witness_V7 := {
  w7_kappa_eff       : R;
  w7_entropy_eff     : R;
  w7_mass_eff        : R;
  w7_inertial_idx    : R;
  w7_global_decision : string;
}.

(*
  Matcher tra witness parziale e bus pieno v7.
*)
Definition witness_matches_bus_v7
           (w : LM_Witness_V7)
           (m : LMetrics_v7)
  : Prop :=
     w.(w7_kappa_eff)       = m.(v7_kappa_eff)
  /\ w.(w7_entropy_eff)     = m.(v7_entropy_eff)
  /\ w.(w7_mass_eff)        = m.(v7_mass_eff)
  /\ w.(w7_inertial_idx)    = m.(v7_inertial_idx)
  /\ w.(w7_global_decision) = m.(v7_global_decision).

(*
  Ogni witness può generare almeno una metrica coerente V7.
  I campi mancanti vengono defaultizzati a 0 o stringa dummy.
*)
Lemma witness_v7_to_bus_exists :
  forall w : LM_Witness_V7,
    exists m : LMetrics_v7, witness_matches_bus_v7 w m.
Proof.
  intros w.
  refine (ex_intro _ (Build_LMetrics_v7
    w.(w7_kappa_eff)
    w.(w7_entropy_eff)
    0%R         (* V0 *)
    0%R         (* a_min *)
    0%R         (* p_tunnel *)
    0%R         (* P_success *)
    1%R         (* gamma_dilation *)
    "EUCLIDEAN" (* time_regime *)
    w.(w7_mass_eff)
    w.(w7_inertial_idx)
    0%R         (* risk_index *)
    "UNKNOWN"   (* risk_class *)
    0%R         (* chi_compactness *)
    false       (* horizon_flag *)
    "META"      (* meta_label *)
    w.(w7_global_decision)
    "NONE"      (* global_color *)
    1%R         (* global_score *)
  ) _).
  repeat split; reflexivity.
Qed.

Definition witness_v7_json_acceptable (w : LM_Witness_V7) : Prop :=
  exists m, witness_matches_bus_v7 w m.

