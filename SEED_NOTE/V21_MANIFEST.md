V21 — MEMORY & TREND LAYER

Aggiunte introdotte:
- l21_memory_core        → log append-only degli stati informazionali
- l21_trend_classifier   → classifica SAFE / ACCESS / BH recenti
- l21_export_memory      → produce sommario e lo scrive su file

Principi rispettati:
- nessuna modifica retroattiva agli strati V13–V20
- compatibilità totale col pipeline attuale
- directory isolata (V21_NEXT + V21_MEMORY)
- evoluzione monotona, non invasiva

Capacità ottenute:
- introspezione temporale locale
- interpretazione della storia
- fondamento per attrattori, stagionalità, adattamento V22+

Stato: ALL GREEN

