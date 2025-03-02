# Inspired from https://github.com/palmskog/coq-program-verification-template

all: partial-fun logrel

autosubst:
	autosubst -f -s ucoq -v ge813 -p ./theories/AutoSubst/Ast_preamble -no-static -o ./theories/AutoSubst/Ast.v ./theories/AutoSubst/Ast.sig
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