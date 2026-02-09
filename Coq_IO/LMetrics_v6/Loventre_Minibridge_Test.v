From Stdlib Require Import Reals.
From Stdlib Require Import String.

From LMetrics_v6 Require Import
  LMetrics_v6_types
  witness_json_m_v6_seed_01
  witness_json_m_v6_seed_02
  witness_json_m_v6_seed_03.

(* Mini-Bridge classification *)
Inductive MClass :=
  | MB_P          (* P_like *)
  | MB_PA         (* P_accessible *)
  | MB_BH.        (* NP_blackhole *)

(* classifier triviale per mini bridge:
   useremo risk_index perché è presente in TUTTI i witness v6 *)
Definition classify (m : LMetrics) : MClass :=
  if Rlt_dec (risk_index m) 0.30 then MB_P
  else if Rlt_dec (risk_index m) 0.60 then MB_PA
  else MB_BH.

(* Test per le tre istanze DIMACS *)
Definition class_01 := classify witness_json_m_v6_seed_01.
Definition class_02 := classify witness_json_m_v6_seed_02.
Definition class_03 := classify witness_json_m_v6_seed_03.

(* Output visibile *)
Eval vm_compute in class_01.
Eval vm_compute in class_02.
Eval vm_compute in class_03.

