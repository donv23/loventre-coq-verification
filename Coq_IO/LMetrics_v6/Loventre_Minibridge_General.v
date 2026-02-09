From Stdlib Require Import Reals String List.
Import ListNotations.

From LMetrics_v6 Require Import LMetrics_v6_types
                             witness_json_m_v6_seed_01
                             witness_json_m_v6_seed_02
                             witness_json_m_v6_seed_03.

(* Classe di output ridotta *)
Inductive MClass :=
  | MB_P
  | MB_PA
  | MB_BH.

(* Estrae dai witness le componenti numeriche rilevanti
   useremo: kappa_eff ed entropy_eff *)
Definition mb_eval (m : LMetrics) : MClass :=
  if Rlt_dec (kappa_eff m) (entropy_eff m)
  then MB_P
  else if Rlt_dec (entropy_eff m) (mass_eff m)
       then MB_PA
       else MB_BH.

(* Lista dei witness disponibili *)
Definition mb_inputs : list LMetrics :=
  [ witness_json_m_v6_seed_01;
    witness_json_m_v6_seed_02;
    witness_json_m_v6_seed_03 ].

(* Produciamo lista classificazioni *)
Definition mb_outputs : list MClass :=
  map mb_eval mb_inputs.

