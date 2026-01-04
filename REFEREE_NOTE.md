**Nota per i referee**

Il repository `loventre-coq-verification` contiene la verifica formale in Coq del nucleo logico del *Trattato Ultimissimo*.
Il codice è congelato nel branch `release-2026-01-04-ultimissimo`, identificato dal tag `v4-freeze-2026-01-04`.

La struttura del repository segue una governance epistemica esplicita e tracciata.
Le assunzioni sono organizzate secondo una ladder dichiarata (A1, A2, A3):

* le proprietà strutturali sono dimostrate formalmente;
* le dinamiche ammissibili sono isolate e non incorporate nelle definizioni;
* ogni ipotesi residua è esplicitamente localizzata come assunzione dichiarata, senza definizioni per negazione né costruzioni circolari.

In particolare, l’esistenza di profili *P-like-accessible* è trattata come assunzione residua esplicita (Ladder A3), separata dalle dimostrazioni geometriche e dalla catena di ostruzione strutturale.

Il repository non include alcun motore algoritmico o numerico.
Sono presenti esclusivamente definizioni astratte, lemmi, teoremi e strumenti di audit formale.

La verificabilità è garantita dagli script di controllo inclusi.
Il freeze assicura una base stabile, riproducibile e semanticamente controllata per la valutazione.

