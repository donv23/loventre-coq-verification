# LOVENTRE — SEED T_Loventre_v3_Prop_Abstract & Modulare (Dicembre 2025)

## 0. Scopo

Questo seed documenta la nascita e il ruolo del modulo Coq:

- `03_Main/Loventre_T_Loventre_v3_Prop_Experimental.v`

che introduce una **versione astratta e modulare** delle ipotesi:

- `T_Loventre_v3_Prop`

senza appoggiarsi ai dettagli concreti della Geometry v3
(bus, JSON, witness, ecc.).

L’obiettivo è:

- isolare la **struttura logica pura** delle ipotesi T_Loventre_v3_Prop,
- dimostrare in Coq una **equivalenza formale**:

  ```text
  T_Loventre_v3_Prop_Abstract  <->  (P_side ∧ NPbh_side)

