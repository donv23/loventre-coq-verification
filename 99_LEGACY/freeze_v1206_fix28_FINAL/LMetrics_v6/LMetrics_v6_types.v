From Stdlib Require Import Reals.
From Stdlib Require Import String.

(* Tipi principali *)
Inductive RiskClass := LOW | MEDIUM | HIGH.
Inductive LoventreDecision := SAFE | UNSAFE.
Inductive Color := RED | YELLOW | GREEN.

(* Tipi logici SAFE/unsafe estesi *)
Inductive SoftFlag := HARD | SOFT.

(* Meta label placeholder *)
Definition meta_v6_seed := 1.

(* Tipi base per il witness *)
Record LMetrics := mkLMetrics {
  kappa_eff               : R;
  entropy_eff             : R;
  mass_eff                : R;
  inertial_idx            : R;
  risk_index              : R;
  risk_class              : RiskClass;
  loventre_global_decision: LoventreDecision;
  loventre_global_color   : Color;
  loventre_global_score   : R;
  meta_label              : nat;
  soft_flag               : SoftFlag;
  source_file             : string
}.

