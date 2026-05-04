(*
  TEST — LAB-12.5
  Verifica che la rigidità globale condizionata
  NON sia dimostrabile per vacuità.
*)

Load "LAB/LAB_12_5/LAB_12_5_Conditional_Global_Rigidity.v".

Fail Lemma Conditional_GlobalRigid_is_trivial :
  GlobalRigid_reach_cond.

