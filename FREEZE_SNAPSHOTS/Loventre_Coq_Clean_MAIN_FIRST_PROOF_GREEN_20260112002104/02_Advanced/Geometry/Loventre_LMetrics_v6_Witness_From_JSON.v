(*
  Loventre_LMetrics_v6_Witness_From_JSON.v
  Witness estratti da JSON v6 tramite CLI Python
  Congelamento: Gennaio 2026
*)

From Stdlib Require Import ZArith String List.
Import ListNotations.
Open Scope Z_scope.

From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v6_Structure.
Import Loventre_LMetrics_V6_Structure.

(* Witness record: ridotto ai campi che il JSON CLI garantisce *)
Record LM_Witness_V6 := {
  w_kappa_eff      : option Z;
  w_entropy_eff    : option Z;
  w_mass_eff       : Z;
  w_inertial_idx   : option Z;
  w_global_decision : string;
}.

(* Confronto witness ↔ bus *)
Definition witness_matches_bus
           (w: LM_Witness_V6)
           (m: LMetrics_v6)
  : Prop :=
     w.(w_kappa_eff) = m.(kappa_eff)
  /\ w.(w_entropy_eff) = m.(entropy_eff)
  /\ w.(w_mass_eff) = m.(mass_eff)
  /\ w.(w_inertial_idx) = m.(inertial_idx)
  /\ w.(w_global_decision) = m.(loventre_global_decision).

(* Placeholder: ogni witness può generare almeno un bus coerente *)
Lemma witness_to_bus_exists :
  forall (w : LM_Witness_V6),
    exists (m: LMetrics_v6), witness_matches_bus w m.
Proof.
  intros w.
  refine (ex_intro _ (Build_LMetrics_v6
                        w.(w_kappa_eff)
                        w.(w_entropy_eff)
                        w.(w_mass_eff)
                        w.(w_inertial_idx)
                        (* campi non presenti nel JSON: dummy *)
                        w.(w_inertial_idx) (* risk_index *)
                        "UNKNOWN" (* risk_class *)
                        w.(w_global_decision)
                        "GREEN"
                        1%Z
                        None None None None None None
                        "meta_stub"
                        None None
                     ) _).
  repeat split; reflexivity.
Qed.

(* Witness JSON accettabile se esiste almeno un bus coerente *)
Definition witness_json_acceptable (w: LM_Witness_V6) : Prop :=
  exists m, witness_matches_bus w m.

