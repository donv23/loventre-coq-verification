(** * Loventre_Theorem_v2_Witness_Bridge
    Ponte v2: esistenza di un witness NP_like-black-hole NON SAFE

    Scopo di questo file:
      - Estrarre dal teorema v1 la sola parte
          "esiste un witness NP_like-black-hole non SAFE"
        come enunciato riusabile e leggibile,
        allineato con il guardiano NP-critico lato Python.

      - Non aggiungiamo nuova logica: riusiamo soltanto
        Loventre_Theorem_v1_from_contract
        e spacchettiamo la sua congiunzione.

    Collegamento concettuale con il motore Python:
      - I JSON NP_critici
          metrics_SAT_crit16_demo_with_global.json
          metrics_TSP_crit28_demo_with_global.json
        sono classificati come
          NP_like_crit_complexity
        e soddisfano operativamente:
          loventre_global_decision <> GD_safe
          loventre_global_color    <> GC_green
        come verificato da:
          loventre_policy_spec_check.py
          loventre_np_critical_guard.py

      - Questo teorema dice in modo astratto:
          sotto lo stesso contratto usato per v1,
          esiste almeno una metrica NP_like-black-hole
          che NON è classificata SAFE.
 *)

From Loventre_Geometry Require Import
  Loventre_LMetrics_Policy_SAFE_Spec
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs
  Loventre_Theorem_v1.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** Alias per il modulo di esistenza, come in Loventre_LMetrics_Policy_Theorem *)
Module Ex := Loventre_LMetrics_Existence_Summary.

(** ** Enunciato bridge: esistenza di un NP_like NON SAFE *)

Definition Loventre_Theorem_v2_Witness_Bridge_Statement : Prop :=
  exists m : LMetrics,
    Ex.is_NP_like_black_hole m /\
    loventre_global_decision m <> GD_safe.

(** ** Teorema: dal contratto (Core + SAFE) al witness NP_like NON SAFE

    Usiamo semplicemente:
      - Loventre_Theorem_v1_from_contract
      - la definizione di Loventre_Theorem_v1_Statement
    e ne estraiamo la seconda congiunzione.
 *)

Theorem Loventre_Theorem_v2_Witness_Bridge_from_contract :
  Loventre_Policy_Core_Program ->
  policy_SAFE_implies_green_global ->
  Loventre_Theorem_v2_Witness_Bridge_Statement.
Proof.
  intros Hcore Hsafe.
  pose proof (Loventre_Theorem_v1_from_contract Hcore Hsafe) as Hv1.
  unfold Loventre_Theorem_v1_Statement in Hv1.
  destruct Hv1 as [_ Hwitness].
  (* Hwitness ha esattamente la forma:
       exists m : LMetrics,
         Ex.is_NP_like_black_hole m /\
         loventre_global_decision m <> GD_safe.
     che coincide con Loventre_Theorem_v2_Witness_Bridge_Statement.
   *)
  exact Hwitness.
Qed.

