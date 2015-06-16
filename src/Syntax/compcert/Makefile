COQLIBS=-I ../../../lib/GraphBasics -I ../../../lib/metalib-20090714 \
	-R ../../../lib/Coq-Equations-8.4/theories Equations -I ../../../lib/Coq-Equations-8.4/src \
 -I .

MAKECOQ=make -f Makefile.coq COQLIBS="$(COQLIBS)"

all: theories

theories: Makefile.coq 
	+$(MAKECOQ)

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq

clean:
	make -f Makefile.coq clean
