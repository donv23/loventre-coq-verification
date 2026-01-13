(*
  Loventre_Invariance_C.v
  -----------------------
  Formalizzazione minimale del principio di invarianza C.

  - C è un descrittore di regime (non decisionale)
  - Non introduce assiomi computazionali
  - Non interagisce con P / NP
*)

From Stdlib Require Import Reals.
From Stdlib Require Import Logic.FunctionalExtensionality.

(* Tipo astratto delle metriche Loventre *)
Parameter LMetrics : Type.

(* Regime operativo astratto *)
Parameter C_regime : LMetrics -> Type.

(* Valore astratto di C *)
Parameter C_value : LMetrics -> R.

(* Due metriche sono nello stesso regime *)
Definition same_C_regime (m1 m2 : LMetrics) : Prop :=
  C_regime m1 = C_regime m2.

(* ============================== *)
(* Lemma di invarianza di regime *)
(* ============================== *)

Lemma C_invariant_on_regime :
  forall m1 m2 : LMetrics,
    same_C_regime m1 m2 ->
    C_value m1 = C_value m2.
Proof.
  intros m1 m2 Hreg.
  (* Invarianza assunta come proprietà strutturale *)
  (* Nessuna computazione richiesta *)
Admitted.

(* Nota:
   Questo lemma è deliberatamente:
   - Admitted
   - locale
   - auditabile

   In futuro potrà essere:
   - dimostrato (se C viene formalizzato)
   - oppure mantenuto come assunzione geometrica
*)

