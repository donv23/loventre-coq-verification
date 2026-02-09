# Loventre Engine – Hysteresis Observability Note (v1)

## Stato
CANONICO — gennaio 2026

## Scopo
Questa nota fissa in modo formale il significato del campo
`hysteresis_detected` nel Loventre Engine e chiarisce i limiti
osservativi del modello quando lavora su snapshot di metriche
(JSON singoli, senza storia temporale).

---

## Contesto

Il Loventre Engine opera su istanze statiche di metriche
(`metrics.json`), ciascuna delle quali rappresenta un singolo
punto nello spazio degli stati informazionali.

In questo regime:
- non è disponibile la storia del sistema
- non è osservabile il percorso che ha condotto allo stato corrente
- non è ricostruibile l’ordine temporale delle transizioni

---

## Definizione chiave

**Isteresi**  
= proprietà del *percorso* nello spazio degli stati,  
non del punto finale.

Formalmente:
> Due sistemi che condividono lo stesso snapshot finale
> possono avere storie incompatibili (con o senza isteresi).

---

## Conseguenza fondamentale

Da un singolo snapshot:
- non è possibile distinguere tra
  - collasso irreversibile
  - collasso con memoria (isteresi)
  - collasso temporaneo

Questa indecidibilità è strutturale e inevitabile.

---

## Interpretazione corretta di `hysteresis_detected`

Nel Loventre Engine:


