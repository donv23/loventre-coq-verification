(*
  TEST — LAB-12.6
  Verifica che la rigidità strutturata
  NON sia dimostrabile per vacuità.
*)

Load "LAB/LAB_12_6/LAB_12_6_Structured_Global_Rigidity.v".

Fail Lemma Structured_GlobalRigid_is_trivial :
  forall (S : System) (TB : TwoBasins S),
    GlobalRigid_struct S TB.

