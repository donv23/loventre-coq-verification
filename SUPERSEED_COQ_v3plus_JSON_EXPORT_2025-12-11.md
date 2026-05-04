# SUPERSEED COQ — LOVENTRE v3/v3+ + JSON EXPORT (11 dicembre 2025)

## 1. REGOLE AUREE (OPERATIVE, NAMESPACE, JSON, LMetrics)

### 1.1. Lingua, stile, strumenti

- Tutto il lavoro concettuale e i commenti restano **in italiano**.
- Si lavora **solo da terminale** con:
  - `cd` sempre esplicito alla root o alla cartella interessata.
  - `nano` per modificare i file `.v` (niente editor grafici).
- **Niente patch “a mano” spezzate**:
  - ogni modifica è sempre un file completo pronto da incollare (o incollato dentro `nano`).
- Dopo ogni modifica Coq, si compila subito il file toccato con `coqc`:
  - niente raffiche di cambi senza test.

### 1.2. Namespace Coq v3/v3+ (scelta definitiva)

Per la famiglia v3 / v3+ di `Loventre_Coq_Clean`:

```bash
-Q ../01_Core Loventre_Core
-Q ../02_Advanced/Geometry Loventre_Geometry
-Q . Loventre_Main

