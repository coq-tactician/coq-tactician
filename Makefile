all: Makefile.coq .merlin
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf .merlin src/tactician.o src/tactician.cmx src/tactician.cmi

make install-utility:
	@echo "Installing Tactician utility"
	@if [[ -v OPAM_BIN ]];\
	then\
		cp tactician $(OPAM_BIN)/tactician;\
	else\
		echo "Error: Variable OPAM_BIN is not set"; exit 1;\
	fi

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject: ;

%: Makefile.coq
	+make -f Makefile.coq $@

.PHONY: all clean
