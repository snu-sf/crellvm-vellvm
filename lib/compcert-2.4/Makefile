# COQTHEORIES  := $(shell find . -name "*.v")
COQTHEORIES  := backend/*.v common/*.v flocq/Appli/*.v flocq/Calc/*.v flocq/Core/*.v flocq/Prop/*.v old/*.v lib/*.v ia32/Archi.v
COQMODULE    := compcert

.PHONY: all theories clean

all: theories

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R . $(COQMODULE)"; \
   echo "-R ../metalib metalib"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

theories: Makefile.coq
	$(MAKE) -f Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
