DEFINITIONS := Meta Syntax Dynamic Types WellFormedness
PROOFS := ListExtras Shared MetaProp SyntaxProp DynamicProp TypesProp WellFormednessProp Locking Progress Preservation Soundness
LIBS := CpdtTactics LibTactics
MODULES := $(DEFINITIONS) $(PROOFS) $(LIBS)

VS      := $(MODULES:%=%.v)

.PHONY: coq clean count

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

count: 
	@echo Definitions:
	@cat $(DEFINITIONS:%=%.v) | wc
	@echo Properties:
	@cat $(PROOFS:%=%.v) | wc
	@echo Total:
	@cat $(DEFINITIONS:%=%.v) $(PROOFS:%=%.v) | wc
	@echo
	@echo Libraries:
	@cat $(LIBS:%=%.v) | wc


Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq