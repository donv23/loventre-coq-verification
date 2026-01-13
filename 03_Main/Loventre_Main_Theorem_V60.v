(** Loventre_Main_Theorem_V60.v
    Dimostrazione esistenziale finale core v3 Clean (Jan 2026)
*)

From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Predicates
  Loventre_Main_Witness
  Loventre_Main_Witness_2SAT
  Loventre_Main_Classes.

(** Theorem V60:
    Esistono tre istanze mP, mA, mB tali che:
      - mP è P_like (SAFE)
      - mA è P_accessible_like (SAFE ma non BlackHole)
      - mB è NP_blackhole_like (BlackHole)
*)

Theorem Loventre_V60_Existence_Core :
  exists mP mA mB,
    In_P_like mP /\
    In_P_accessible_like mA /\
    In_NP_blackhole_like mB.
Proof.
  (** Scegliamo i witness canonici *)
  exists m_seed_minimal.
  exists m_seed_grid.
  exists m_2SAT_crit.

  repeat split.

  - (** mP è P_like *)
    unfold In_P_like.
    apply SAFE_seed_minimal.

  - (** mA è P_accessible_like *)
    unfold In_P_accessible_like.
    split.
    + apply SAFE_seed_grid.
    + apply not_blackhole_seed_grid.

  - (** mB è NP blackhole *)
    unfold In_NP_blackhole_like.
    apply BH_seed_2SAT_crit.
Qed.


