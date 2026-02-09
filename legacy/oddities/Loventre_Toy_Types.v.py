cd ~
cd "Desktop"
mkdir -p "LOVENTRE PROJECT"
cd "LOVENTRE PROJECT"

cat > Loventre_Toy_Types.v << 'EOF'
From Coq Require Import List.
Import ListNotations.

(** Tipi di base per il modello toy del Loventre Engine *)

Inductive parameter : Set := P1 | P2 | P3.
Inductive factor    : Set := F1 | F2 | F3.

Definition params : Set := (parameter * factor)%type.

Definition all_params : list params :=
  [ (P1, F1); (P1, F2); (P1, F3);
    (P2, F1); (P2, F2); (P2, F3);
    (P3, F1); (P3, F2); (P3, F3) ].

(** Regimi 1D e multicanale *)

Inductive regime1D : Set :=
  | StableLowVariation
  | Intermediate
  | CriticalHighEntropy.

Inductive mc_regime : Set :=
  | SynchronizedLowSpread
  | SynchronizedHighSpread
  | DesynchronizedHighSpread
  | MixedIntermediate.

(** Pattern C: label e flag *)

Inductive patternC_label : Set :=
  | RegularConfiguration
  | GeometricPrecriticalConfiguration
  | FullyCriticalConfiguration
  | MixedConfiguration.

Record patternC_flags := {
  flag_is_fully_critical      : bool ;
  flag_has_geometric_precrit  : bool ;
  flag_is_regular             : bool
}.

(** Signature corta / lunga e signature critica complessiva *)

Record short_signature := {
  short_regime1D        : regime1D ;
  short_patternC_label  : patternC_label ;
  short_patternC_flags  : patternC_flags ;
  short_channels_spread : nat
}.

Record long_signature := {
  long_regime1D        : regime1D ;
  long_mc_regime       : mc_regime ;
  long_is_mc_critical  : bool ;
  long_channels_spread : nat
}.

Record critical_signature := {
  sig_short : short_signature ;
  sig_long  : long_signature
}.

(** Per ora la signature è lasciata astratta: la riempiremo in seguito
    usando i risultati sperimentali del motore Python. *)

Parameter signature : params -> critical_signature.

Definition short_sig_of (p : params) : short_signature :=
  sig_short (signature p).

Definition long_sig_of (p : params) : long_signature :=
  sig_long (signature p).

Definition short_patternC_of (p : params) : patternC_label :=
  short_patternC_label (short_sig_of p).

Definition short_flags_of (p : params) : patternC_flags :=
  short_patternC_flags (short_sig_of p).

Definition long_mc_regime_of (p : params) : mc_regime :=
  long_mc_regime (long_sig_of p).

Definition long_is_mc_critical_of (p : params) : bool :=
  long_is_mc_critical (long_sig_of p).

(** Partizione dello spazio dei parametri in regioni regolare / precritica / critica. *)

Definition R_reg (p : params) : Prop :=
  p = (P1, F1) \/ p = (P1, F2) \/ p = (P2, F1).

Definition R_pre (p : params) : Prop :=
  p = (P2, F2) \/ p = (P3, F1).

Definition R_crit (p : params) : Prop :=
  p = (P2, F3) \/ p = (P3, F2) \/ p = (P3, F3).

(** Helper logici legati al Pattern C *)

Definition is_fully_critical_pattern (p : params) : bool :=
  match short_patternC_of p with
  | FullyCriticalConfiguration => true
  | _ => false
  end.

Definition is_geometric_precritical_pattern (p : params) : bool :=
  match short_patternC_of p with
  | GeometricPrecriticalConfiguration => true
  | _ => false
  end.

Definition is_regular_pattern (p : params) : bool :=
  match short_patternC_of p with
  | RegularConfiguration => true
  | _ => false
  end.

(** Helper per la "multichannel explosiveness".
    NB: la soglia effettiva (quanto spread è "enorme") verrà gestita
    più avanti, quando avremo i valori concreti dalla tabella critica. *)

Definition has_explosive_multichannel (p : params) : Prop :=
  long_is_mc_critical_of p = true
  /\ long_mc_regime_of p = SynchronizedHighSpread.

(** Definizioni astratte P-like / NP-like (nessun lemma ancora). *)

Definition P_like (p : params) : Prop :=
  (R_reg p /\ is_regular_pattern p = true)
  \/
  (R_pre p /\ is_geometric_precritical_pattern p = true).

Definition NP_like (p : params) : Prop :=
  R_crit p
  /\ is_fully_critical_pattern p = true
  /\ has_explosive_multichannel p.
EOF
