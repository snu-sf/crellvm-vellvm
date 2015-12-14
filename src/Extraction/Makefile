MAKECOQ=make -f Makefile.coq

all: extraction

extraction: Makefile.coq
	+$(MAKECOQ)

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq

clean:
	make -f Makefile.coq clean
