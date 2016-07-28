OTT ?= ott

COQMODULE    := Vellvm
COQTHEORIES  := $(shell ls \
  src/GraphBasics/*.v \
  src/Vellvm/Dominators/*.v \
  src/Vellvm/ott/*.v) \
  src/Vellvm/analysis.v src/Vellvm/datatype_base.v src/Vellvm/dopsem.v src/Vellvm/events.v src/Vellvm/external_intrinsics.v src/Vellvm/genericvalues_inject.v src/Vellvm/genericvalues_props.v src/Vellvm/genericvalues.v src/Vellvm/infrastructure.v src/Vellvm/infrastructure_props.v \
	src/Vellvm/memory_sim.v src/Vellvm/opsem_props.v src/Vellvm/opsem.v src/Vellvm/opsem_wf.v src/Vellvm/ott_list_core.v src/Vellvm/ott_list_eq_dec.v \
	src/Vellvm/static.v src/Vellvm/syntax.v src/Vellvm/monad.v src/Vellvm/syntax_base.v src/Vellvm/tactics.v src/Vellvm/targetdata.v src/Vellvm/targetdata_props.v src/Vellvm/trace.v \
	src/Vellvm/typing_rules.v src/Vellvm/typings_props.v src/Vellvm/typings.v src/Vellvm/vellvm.v src/Vellvm/vellvm_tactics.v src/Vellvm/memory_props.v src/Vellvm/program_sim.v src/Vellvm/util.v src/Vellvm/maps_ext.v

COQEXTRACT	:= src/Extraction/extraction_dom.v src/Extraction/extraction_core.v 

.PHONY: all metalib cpdtlib theories clean

all: theories

init:
	git clone git@github.com:snu-sf/cpdtlib.git lib/cpdtlib
	git clone git@github.com:snu-sf/metalib.git lib/metalib

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src $(COQMODULE)"; \
   echo "-R lib/metalib metalib"; \
   echo "-R lib/cpdtlib Cpdt"; \
   echo "-R lib/compcert-2.4 compcert"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

metalib: lib/metalib
	$(MAKE) -C lib/metalib

cpdtlib: lib/cpdtlib
	$(MAKE) -C lib/cpdtlib

compcert: lib/compcert-2.4 metalib
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

theories: metalib cpdtlib compcert Makefile.coq src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v
	$(MAKE) -f Makefile.coq

extract: theories $(COQEXTRACT)
	$(MAKE) -C src/Extraction
	cd src/Extraction; ./fixextract.py

%.vo: Makefile.coq src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v
	$(MAKE) -f Makefile.coq "$@"

clean: Makefile.coq
	rm -f src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v 
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	$(MAKE) -C src/Extraction clean
