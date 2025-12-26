(** ******************************************************************* **)
(** * Loventre_Main_Theorem_Instance.v                                  **)
(**                                                                     **)
(** Istanziazione astratta di Loventre_Main_Theorem.                    **)
(**                                                                     **)
(** Non usiamo ancora i moduli concreti Geometry/Main:                   **)
(**   - trattiamo LMetrics, i profili e la Policy come parametri;       **)
(**   - assumiamo due ipotesi concrete di esistenza;                    **)
(**   - applichiamo il teorema astratto Loventre_Main_Theorem.          **)
(**                                                                     **)
(** In una fase successiva queste Variable/Hypothesis verranno          **)
(** rimpiazzate dai tipi e dai lemmi reali (LMetrics, witness v2, SAFE  **)
(** separation, ecc.).                                                  **)
(** ******************************************************************* **)

From Coq Require Import Init.Logic.
Require Import Loventre_Main.Loventre_Main_Theorem.

Section Loventre_Main_Concrete.

  (** Parametri astratti: qui, in futuro, verranno collegati
      ai tipi/profili/Policy reali del progetto Loventre. *)

  Variable LMetrics : Type.

  Variable P_like_complexity_profile  : LMetrics -> Prop.
  Variable P_like_accessible_profile  : LMetrics -> Prop.
  Variable NP_like_crit_profile       : LMetrics -> Prop.

  Variable GlobalDecision : Type.
  Variable loventre_global_decision : LMetrics -> GlobalDecision.
  Variable GD_safe : GlobalDecision.

  (** Ipotesi "concrete" (in questa fase ancora astratte) che
      dovranno essere garantite dai witness reali e dai teoremi v2. *)

  Hypothesis Loventre_existence_P_profiles_concrete :
    exists (m_P m_Pacc : LMetrics),
      P_like_complexity_profile m_P /\
      P_like_accessible_profile m_Pacc.

  Hypothesis Loventre_existence_NPcrit_not_safe_concrete :
    exists (m_NP : LMetrics),
      NP_like_crit_profile m_NP /\
      loventre_global_decision m_NP <> GD_safe.

  (** Teorema concreto (parametrico): se valgono le due ipotesi
      di esistenza, allora vale la proposizione principale
      Loventre_Main_Prop per questi dati. *)

  Theorem Loventre_Main_Theorem_concrete :
    Loventre_Main_Prop
      LMetrics
      P_like_complexity_profile
      P_like_accessible_profile
      NP_like_crit_profile
      GlobalDecision
      loventre_global_decision
      GD_safe.
  Proof.
    apply (Loventre_Main_Theorem
             LMetrics
             P_like_complexity_profile
             P_like_accessible_profile
             NP_like_crit_profile
             GlobalDecision
             loventre_global_decision
             GD_safe
             Loventre_existence_P_profiles_concrete
             Loventre_existence_NPcrit_not_safe_concrete).
  Qed.

End Loventre_Main_Concrete.

(** ******************************************************************* **)
(** Fine di Loventre_Main_Theorem_Instance.v                            **)
(** ******************************************************************* **)

