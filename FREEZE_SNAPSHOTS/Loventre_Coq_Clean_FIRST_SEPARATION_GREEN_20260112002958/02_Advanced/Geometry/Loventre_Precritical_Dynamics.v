(*
  Loventre — Precritical Dynamics
  v1 — Dicembre 2025

  Questo modulo introduce concetti DINAMICI
  osservativi sulla pre-criticità.

  Nessun impatto su:
  - decisioni
  - SAFE
  - separazioni CANON
*)

From Stdlib Require Import List.
Import ListNotations.

(* Osservazioni minime su uno step *)
Record PrecriticalObs := {
  pre_critical_flag : bool;
  horizon_flag : bool;
}.

(* Uno step pre-critico non terminale *)
Definition is_precritical_nonterminal (o : PrecriticalObs) : Prop :=
  pre_critical_flag o = true /\ horizon_flag o = false.

(* Persistenza pre-critica:
   esistono almeno due step distinti
   pre-critici non terminali *)
Definition has_precritical_persistence
  (seq : list PrecriticalObs) : Prop :=
  exists o1 o2,
    o1 <> o2 /\
    In o1 seq /\
    In o2 seq /\
    is_precritical_nonterminal o1 /\
    is_precritical_nonterminal o2.

(* Nota:
   - questa proprietà NON implica collasso
   - NON implica NP_like
   - è puramente dinamica
*)

