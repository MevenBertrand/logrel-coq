# Inspired from https://github.com/palmskog/coq-program-verification-template

all: partial-fun logrel

autosubst:
	autosubst -s ucoq -v ge813 -p ./theories/AutoSubst/Ast_preamble ./theories/AutoSubst/Ast.sig -o ./theories/AutoSubst/Ast.v

partial-fun:
	@+$(MAKE) -C coq-partialfun all

logrel: partial-fun Makefile.coq
	@+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@+$(MAKE) -C coq-partialfun clean
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force partial-fun logrel autosubst