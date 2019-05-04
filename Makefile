# Coq sources
COQDIR = coq
COQINCLUDES=$(foreach d, $(COQDIR), -R $(d) Examples) -R $(EXTRACTDIR) Extract
COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQEXEC="$(COQBIN)coqtop" -q -w none $(COQINCLUDES) -batch -load-vernac-source


COQFILES :=
VFILES := $(COQFILES:%=coq/%.v)
VOFILES := $(COQFILES:%=coq/%.vo)

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) coq
coq: $(VOFILES)

%.vo: %.v
	@echo "COQC $*.v"

depend: $(VFILES) 
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend


.PHONY: clean test restore
print-includes:
	@echo $(COQINCLUDES)

clean:
	rm -f .depend
	rm -f $(VOFILES)
	

