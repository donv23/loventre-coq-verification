(**
  CANON_Phase_Index.v

  Entry-point pubblico delle fasi CANON.

  Esporta:
  - predicati di fase (SAFE / WARNING / BLACKHOLE)
  - lemma di totalità

  Nessuna logica nuova.
  Nessuna dipendenza SHADOW.
  Compatibile con il CANON stabile.

  Dicembre 2025
*)

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_CANON
  Loventre_LMetrics_Phase_CANON_Totality.

Import Loventre_LMetrics_Phase_CANON.

Export Loventre_LMetrics_Phase_CANON.
Export Loventre_LMetrics_Phase_CANON_Totality.

