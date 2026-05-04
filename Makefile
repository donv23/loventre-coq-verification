# Variabili di configurazione
COQ_BIN = coqc
COQ_MAKEFILE = _CoqProject

# Cartelle del progetto
CORE_DIR = 01_Core
ADVANCED_DIR = 02_Advanced
MAIN_DIR = 03_Main

# File principali da compilare (modificabile in base alle necessità)
FILES_TO_COMPILE = \
    $(CORE_DIR)/Loventre_Core_Prelude.v \
    $(CORE_DIR)/Loventre_Core.v \
    $(ADVANCED_DIR)/Loventre_LMetrics_Policy_SAFE_Spec.v \
    $(ADVANCED_DIR)/Loventre_LMetrics_Extraction.v \
    $(MAIN_DIR)/Loventre_LMetrics_Policy_Specs.v \
    $(MAIN_DIR)/Loventre_LMetrics_Separation_Theorem.v

# Obiettivi principali
all: compile

# Compilazione dei file .v
compile:
	@echo "Compilazione in corso..."
	@$(COQ_BIN) $(FILES_TO_COMPILE)

# Pulizia dei file generati
clean:
	@echo "Pulizia in corso..."
	@rm -f $(OUTPUT_DIR)/*

# Test di regressione con python
test:
	@echo "Esecuzione dei test..."
	@python3 -m unittest discover -s $(TEST_DIR)

# Obiettivo di build completo (compilazione e test)
build: compile test

# Aggiorna i file di Coq se necessario
update:
	@echo "Aggiornamento dei file Coq..."
	@coq_makefile -f $(COQ_MAKEFILE) -o Makefile.conf
	@make -f Makefile.conf

.PHONY: all compile clean test build update

