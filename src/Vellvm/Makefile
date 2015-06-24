COQLIBS=-I ../../lib/GraphBasics -I ../../lib/metalib-20090714 \
	-R ../../lib/Coq-Equations-8.4/theories Equations -I ../../lib/Coq-Equations-8.4/src \
 -I ../../lib/compcert-2.4/lib -I ../../lib/compcert-2.4/ia32 -I ../../lib/compcert-2.4/common -I ../../lib/compcert-2.4/flocq/Appli -I ../../lib/compcert-2.4/flocq/Calc -I ../../lib/compcert-2.4/flocq/Core -I ../../lib/compcert-2.4/flocq/Prop -I ../../lib/compcert-2.4/old -I ../../lib/compcert-2.4/backend \
 -I . \
 -I ../Syntax

MAKECOQ=make -f Makefile.coq COQLIBS="$(COQLIBS)"

all: theories

theories: Makefile.coq
	+$(MAKECOQ)

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq

clean:
	make -f Makefile.coq clean
