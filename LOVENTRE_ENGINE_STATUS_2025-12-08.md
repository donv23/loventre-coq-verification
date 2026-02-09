# LOVENTRE ENGINE – STATUS SNAPSHOT (2025-12-08)

## 0. Scopo del file

Questo file fotografa lo **stato operativo** del LOVENTRE ENGINE Python al giorno **2025-12-08**, dopo:

- integrazione della **famiglia 2-SAT** (easy / crit);
- introduzione del **Policy Bridge v3 (shim neutro)**;
- allineamento della **regression suite** con:
  - demo principali del motore,
  - check sui JSON 2-SAT,
  - crosscheck JSON ↔ Coq per i 4 witness canonici.

È un file di **stato** (non di design astratto) e serve come riferimento quando in futuro verranno introdotte modifiche strutturali (Policy Bridge v4, nuove famiglie, ecc.).

---

## 1. Contesto tecnico

- Utente: **Vincenzo Loventre**
- Sistema: macOS, shell `zsh`
- Python: `python3` (versione recente, usata come default in tutti gli script)
- Root del progetto Python:

  ```text
  /Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed

