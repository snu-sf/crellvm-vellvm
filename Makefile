OTT ?= ott

COQLIBS=-I src/Vellvm -I src/Vellvm/ott -I src/Vellvm/Dominators \
	-I lib/GraphBasics -I lib/cpdtlib -I lib/metalib-20090714 \
	-I lib/compcert-2.4/backend -I lib/compcert-2.4/common -I lib/compcert-2.4/flocq/Appli/ \
	-I lib/compcert-2.4/flocq/Calc -I lib/compcert-2.4/flocq/Core -I lib/compcert-2.4/flocq/Prop \
	-I lib/compcert-2.4/ia32 -I lib/compcert-2.4/lib -I lib/compcert-2.4/old
MAKECOQ=make -f Makefile.coq COQLIBS="$(COQLIBS)"

all: theories

libs: lib/metalib-20090714
	make -C lib/metalib-20090714

compcert: libs lib/compcert-2.4
	make -C lib/compcert-2.4

depend: Makefile.coq src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v
	+$(MAKECOQ) depend

theories: libs compcert Makefile.coq src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v
	+$(MAKECOQ)

Makefile.coq: Make
	coq_makefile -f Make -o Makefile.coq

%.vo: Makefile.coq src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v
	+$(MAKECOQ) "$@"

clean:
	rm -f src/Vellvm/syntax_base.v src/Vellvm/typing_rules.v 
	make -f Makefile.coq clean
	rm -f Makefile.coq

src/Vellvm/syntax_base.v: src/Vellvm/syntax_base.ott
	cd src/Vellvm && \
	$(OTT) -coq_expand_list_types false -i syntax_base.ott -o syntax_base.v

src/Vellvm/typing_rules.v: src/Vellvm/syntax_base.ott src/Vellvm/typing_rules.ott
	cd src/Vellvm && \
	$(OTT) -merge false -coq_expand_list_types false \
            -i syntax_base.ott -o _tmp_syntax_base.v \
	    -i typing_rules.ott -o typing_rules.v && \
	rm _tmp_syntax_base.v

.PHONY: all clean theories libs
