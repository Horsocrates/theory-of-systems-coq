# Makefile for Theory of Systems — Coq Formalization
#
# Usage:
#   make          — compile all .v files
#   make clean    — remove generated files
#   make count    — count theorems and Admitted
#
# Requires: Coq 8.18+ or Rocq 9.0+

COQMAKEFILE := CoqMakefile

.PHONY: all clean count

all: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)

clean:
	if [ -f $(COQMAKEFILE) ]; then $(MAKE) -f $(COQMAKEFILE) clean; fi
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

count:
	@echo "=== Theorem Count ==="
	@grep -c "Theorem\|Lemma\|Corollary\|Proposition" src/*.v Architecture_of_Reasoning/*.v 2>/dev/null || true
	@echo ""
	@echo "=== Admitted Count ==="
	@grep -c "Admitted" src/*.v Architecture_of_Reasoning/*.v 2>/dev/null || true
	@echo ""
	@echo "=== Total ==="
	@echo -n "Theorems: " && grep -r "Theorem\|Lemma\|Corollary\|Proposition" src/*.v Architecture_of_Reasoning/*.v 2>/dev/null | wc -l
	@echo -n "Admitted: " && grep -r "Admitted" src/*.v Architecture_of_Reasoning/*.v 2>/dev/null | wc -l
