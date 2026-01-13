(** Loventre_Main_All.v
    Mini entry-point per i moduli di alto livello Loventre (03_Main).

    Scopo:
      - Fornire un punto di accesso unico per:
          * la Congettura Loventre,
          * il bridge TM–famiglie,
          * il blocco SAT_crit (famiglia, realizzazione TM, vista congettura,
            incompatibilità TM1/SAT_crit, famiglia metrica LMetrics,
            schema di collasso critico metrico),
          * il blocco TSP_crit (famiglia, realizzazione TM, vista congettura,
            incompatibilità TM1/TSP_crit, famiglia metrica LMetrics,
            schema di collasso critico metrico),
          * una vista unificata dei regimi metrici (is_collapse_regime).
 *)

From Stdlib Require Import Arith.

Require Export Loventre_Conjecture.
Require Export Loventre_TM_Family_Bridge.

(* Blocco SAT_crit *)

Require Export Loventre_SAT_Critical_Family.
Require Export Loventre_TM_SAT_Critical_Realization.
Require Export Loventre_SAT_Critical_Conjecture_View.
Require Export Loventre_SAT_TM_Incompatibility.
Require Export Loventre_SAT_Critical_Metrics.
Require Export Loventre_SAT_Critical_Collapse.

(* Blocco TSP_crit *)

Require Export Loventre_TSP_Critical_Family.
Require Export Loventre_TM_TSP_Critical_Realization.
Require Export Loventre_TSP_Critical_Conjecture_View.
Require Export Loventre_TSP_TM_Incompatibility.
Require Export Loventre_TSP_Critical_Metrics.
Require Export Loventre_TSP_Critical_Collapse.

(* Vista unificata sui regimi metrici *)

Require Export Loventre_Metrics_Regime_View.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

