(** ============================================================= *)
(**                                                               *)
(**   Loventre_LMetrics_Kernel.v                                  *)
(**   Canvas 16 — Fase 2 Kernel                                   *)
(**   Dicembre 2025                                               *)
(**                                                               *)
(**   Obiettivo:                                                  *)
(**   Definire la struttura astratta delle metriche (LMetrics),   *)
(**   preparare il ponte Coq ↔ Python senza introdurre numeri.   *)
(**                                                               *)
(** ============================================================= *)

From Stdlib Require Import Arith.

(**
   NOTA:
   Non importiamo i Canvas 13–15, perché LMetrics è
   un layer fondamentale e minimo.
   Saranno Canvas 17–18 a connettere LMetrics al Meta-Teorema.
*)

Section LMetrics_Kernel.

  (**
     Witness: viene dalle famiglie costruite nel sistema.
     Qui non sappiamo cosa sia, lo lasciamo astratto.
  *)
  Variable Witness : Type.

  (**
     LMetrics è il “profilo informazionale” di un witness.
     Lo trattiamo come struttura con campi proposizionali.
     La scelta minima funzionale è:
       - P_like_flag
       - NP_like_flag
       - reducible_to_P_like
       - reducible_from_P_like
  *)

  Record LMetrics : Type := {
    LM_is_P_like      : Prop;
    LM_is_NP_like     : Prop;
    LM_reducible_to_P : Prop;
    LM_reducible_from_P : Prop
  }.

  (**
     ASSIOMA FUNZIONALE MINIMO:
     Un witness ha un profilo. (Non computiamo il profilo)
  *)
  Variable LProfile_of : Witness -> LMetrics.

  (**
     PROPRIETÀ MINIMA (NON NUMERICA, NON COMPUTAZIONALE):
     P_like ↔ NP_like non può essere simultaneo
     nel profilo di un witness.
  *)
  Definition LM_conflict (m : LMetrics) : Prop :=
    LM_is_P_like m /\ LM_is_NP_like m.

  (**
     Il profilo è “legalmente consistente” se non c’è conflitto.
  *)
  Definition LM_legal (m : LMetrics) : Prop :=
    ~ (LM_conflict m).

  (**
     Profili di witness concreti sono legali.
     (Questo sarà collegato più avanti a Canvas 14 e 15)
  *)
  Definition LM_legal_witness (w : Witness) : Prop :=
    LM_legal (LProfile_of w).

End LMetrics_Kernel.

(** ============================================================
    FINE CANVAS 16 — LMetrics Kernel
    ============================================================ **)

