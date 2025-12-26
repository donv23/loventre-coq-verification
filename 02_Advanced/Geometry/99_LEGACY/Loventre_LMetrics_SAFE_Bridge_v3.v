From Stdlib Require Import List String.
Import ListNotations.

Require Import Loventre_LMetrics_JSON_Link.
Require Import Loventre_LMetrics_SAFE_Tags_v3.
Require Import Loventre_LMetrics_Mini_Theorem_Stack_v2.

(**
  Loventre_LMetrics_SAFE_Bridge_v3

  Scopo:
  - collegare la struttura `Mini_Theorem_Stack_v2`
    (che include la famiglia 2-SAT easy/crit)
    con i tag logici is_SAFE / is_ACCESSIBLE / is_BLACKHOLE;
  - introdurre un lemma di esistenza molto debole
    che assicura che all’interno del Mini Theorem Stack v2
    esista almeno un LMetrics_JSON_Link marcabile
    come SAFE o ACCESSIBLE o BLACKHOLE.

  Nota:
  - non c’è ancora semantica “fisica” dei tag,
    ma serve come step sintattico per il passaggio a v4.
*)

Lemma Loventre_Mini_Theorem_SAFE_Bridge_v3 :
  exists lm, is_SAFE lm \/ is_ACCESSIBLE lm \/ is_BLACKHOLE lm.
Proof.
  (* uso del lemma triviale di copertura definito in SAFE_Tags_v3 *)
  exists (hd (Build_LMetrics_JSON_Link "" "") loventre_json_links).
  apply Loventre_SAFE_ACCESSIBLE_bridge.
Qed.

Print Loventre_Mini_Theorem_SAFE_Bridge_v3.

