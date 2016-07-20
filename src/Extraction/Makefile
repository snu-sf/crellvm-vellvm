COQTHEORIES := extraction_core.v extraction_dom.v

all: extraction

quick: extraction-quick

extraction: Makefile.coq
	$(MAKE) -f Makefile.coq extraction_core.vo
	$(MAKE) -f Makefile.coq extraction_dom.vo

extraction-quick: Makefile.coq
	$(MAKE) -f Makefile.coq extraction_core.vio quick
	$(MAKE) -f Makefile.coq extraction_dom.vio quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-install none"; \
   echo "-R ../../src Vellvm"; \
   echo "-R ../../lib/metalib metalib"; \
   echo "-R ../../lib/cpdtlib Cpdt"; \
   echo "-R ../../lib/compcert-2.4 compcert"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq
