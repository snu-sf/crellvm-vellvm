COQTHEORIES  := $(shell find . -name "*.v")
COQMODULE    := GraphBasics

.PHONY: all theories clean

all: theories

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R . $(COQMODULE) -R ../metalib metalib"; echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

theories: Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
