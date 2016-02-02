OTT ?= ott

COQMODULE    := Vellvm
COQTHEORIES  := $(shell ls \
  lib/GraphBasics/*.v \
  src/Vellvm/*.v \
  src/Vellvm/Dominators/*.v \
  src/Vellvm/ott/*.v)

.PHONY: all metalib cpdtlib theories clean

all: metalib cpdtlib compcert theories

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R . $(COQMODULE)"; \
   echo "-R lib/metalib metalib"; \
   echo "-R lib/cpdtlib cpdtlib"; \
   echo "-R lib/compcert-2.4 compcert"; \
   echo "-R lib/GraphBasics GraphBasics"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

metalib: lib/metalib
	$(MAKE) -C lib/metalib

cpdtlib: lib/cpdtlib
	$(MAKE) -C lib/cpdtlib

compcert: lib/compcert-2.4
	$(MAKE) -C lib/compcert-2.4

src/Vellvm/syntax_base.v: src/Vellvm/syntax_base.ott
	cd src/Vellvm && \
	$(OTT) -coq_expand_list_types false -i syntax_base.ott -o syntax_base.v

src/Vellvm/typing_rules.v: src/Vellvm/syntax_base.ott src/Vellvm/typing_rules.ott
	cd src/Vellvm && \
	$(OTT) -merge false -coq_expand_list_types false \
            -i syntax_base.ott -o _tmp_syntax_base.v \
	    -i typing_rules.ott -o typing_rules.v && \
	rm _tmp_syntax_base.v

theories: Makefile.coq src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v
	$(MAKE) -f Makefile.coq

%.vo: Makefile.coq src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v
	$(MAKE) -f Makefile.coq "$@"

clean:
	rm -f src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v 
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
