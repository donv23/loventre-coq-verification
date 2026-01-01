From Loventre_Axis_C Require Import Loventre_Axis_C_Public_Weak_Index.

(*
  Safety smoke:
  - Il pacchetto Public Weak deve restare minimale.
  - Questi import sono INTENZIONALMENTE attesi FALLIRE.
*)

Fail From Loventre_Axis_C Require Import Loventre_Axis_C_Private_Internal.
Fail From Loventre_Axis_C Require Import LAB_PNP_Incond_Secret.

Goal True. exact I. Qed.

