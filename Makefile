#######################################################################
#                                                                     #
#              The Compcert verified compiler                         #
#                                                                     #
#          Xavier Leroy, INRIA Paris-Rocquencourt                     #
#                                                                     #
#  Copyright Institut National de Recherche en Informatique et en     #
#  Automatique.  All rights reserved.  This file is distributed       #
#  under the terms of the GNU Lesser General Public License as        #
#  published by the Free Software Foundation, either version 2.1 of   #
#  the License, or (at your option) any later version.                #
#  This file is also distributed under the terms of the               #
#  INRIA Non-Commercial License Agreement.                            #
#                                                                     #
#######################################################################

include Makefile.config
include VERSION

BUILDVERSION ?= $(version)
BUILDNR ?= $(buildnr)
TAG ?= $(tag)
BRANCH ?= $(branch)

ifeq ($(wildcard $(ARCH)_$(BITSIZE)),)
ARCHDIRS=$(ARCH)
else
ARCHDIRS=$(ARCH)_$(BITSIZE) $(ARCH)
endif

DIRS := lib common policies $(ARCHDIRS) cfrontend driver export cparser

COQINCLUDES := $(foreach d, $(DIRS), -R $(d) compcert.$(d))

ifeq ($(LIBRARY_FLOCQ),local)
DIRS += flocq/Core flocq/Prop flocq/Calc flocq/IEEE754
COQINCLUDES += -R flocq Flocq
endif

ifeq ($(LIBRARY_MENHIRLIB),local)
DIRS += MenhirLib
COQINCLUDES += -R MenhirLib MenhirLib
endif

# Notes on silenced Coq warnings:
#
# undeclared-scope:
#    warning introduced in 8.12
#    suggested change (use `Declare Scope`) supported since 8.12
# unused-pattern-matching-variable:
#    warning introduced in 8.13
#    the code rewrite that avoids the warning is not desirable
# deprecated-ident-entry:
#    warning introduced in 8.13
#    suggested change (use `name` instead of `ident`) supported since 8.13
# deprecated-hint-rewrite-without-locality:
#    warning introduced in 8.14
#    suggested change (add Global or Local or [#export] modifier)
#    is not supported in 8.13 nor in 8.11, but was supported in 8.9 (go figure)
# deprecated-instance-without-locality:
#    warning introduced in 8.14
#    triggered by Menhir-generated files, to be solved upstream in Menhir

COQCOPTS ?= \
  -w -undeclared-scope \
  -w -unused-pattern-matching-variable \
  -w -deprecated-ident-entry \
  -w -deprecated-hint-rewrite-without-locality

cparser/Parser.vo: COQCOPTS += -w -deprecated-instance-without-locality

COQC="$(COQBIN)coqc" -q $(COQINCLUDES) $(COQCOPTS)
COQDEP="$(COQBIN)coqdep" $(COQINCLUDES)
COQDOC="$(COQBIN)coqdoc"
COQEXEC="$(COQBIN)coqtop" $(COQINCLUDES) -batch -load-vernac-source
COQCHK="$(COQBIN)coqchk" $(COQINCLUDES)
MENHIR=menhir
CP=cp

VPATH=$(DIRS)
GPATH=$(DIRS)

# Flocq

ifeq ($(LIBRARY_FLOCQ),local)
FLOCQ=\
  Raux.v Zaux.v Defs.v Digits.v Float_prop.v FIX.v FLT.v FLX.v FTZ.v \
  Generic_fmt.v Round_pred.v Round_NE.v Ulp.v Core.v \
  Bracket.v Div.v Operations.v Plus.v Round.v Sqrt.v \
  Div_sqrt_error.v Mult_error.v Plus_error.v \
  Relative.v Sterbenz.v Round_odd.v Double_rounding.v \
  BinarySingleNaN.v Binary.v Bits.v
else
FLOCQ=
endif

# General-purpose libraries (in lib/)

VLIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Zbits.v Integers.v Archi.v IEEE754_extra.v Floats.v \
  Parmov.v UnionFind.v Wfsimpl.v \
  Postorder.v FSetAVLplus.v IntvSets.v Decidableplus.v BoolEqual.v \
  Show.v

# Parts common to the front-ends and the back-end (in common/)

COMMON=Errors.v AST.v Linking.v Encoding.v \
  Events.v Globalenvs.v Memdata.v Memory.v Allocator.v \
  AllocatorImpl.v ConcreteAllocator.v \
  Values.v Tags.v Smallstep.v Switch.v Unityping.v \
  Builtins0.v Builtins1.v Builtins.v Determinism.v \

# C front-end modules (in cfrontend/)

CFRONTEND=Ctypes.v Cop.v Csyntax.v Csem.v Ctyping.v Cexec.v \
  Initializers.v InterpreterEvents.v \

# Policy definitions (in policies/) Add new policy files here
# NB Product.v is the (Cartisian) product of multiple policies
POLICIES=NullPolicy.v PVI.v DoubleFree.v HeapProblem.v Product.v Omnilog.v

PROOFS=Simulation.v CompartmentSem.v SemanticsProofs.v

PARSER=Cabs.v Parser.v

# MenhirLib

ifeq ($(LIBRARY_MENHIRLIB),local)
MENHIRLIB=Alphabet.v Automaton.v Grammar.v Interpreter_complete.v \
  Interpreter_correct.v Interpreter.v Main.v Validator_complete.v \
  Validator_safe.v Validator_classes.v
else
MENHIRLIB=
endif

# Putting everything together (in driver/)

DRIVER=Compopts.v

# All source files

FILES=$(VLIB) $(COMMON) $(CFRONTEND) $(POLICIES) $(DRIVER) $(FLOCQ) \
  $(MENHIRLIB) $(PARSER) $(EXPORTLIB)

all:
	@test -f .depend || $(MAKE) depend
	$(MAKE) files
	$(MAKE) extraction
	$(MAKE) ccomp
ifeq ($(INSTALL_COQDEV),true)
	$(MAKE) compcert.config
endif

files: $(FILES:.v=.vo)

proof: files $(PROOFS:.v=.vo)

# Turn off some warnings for compiling Flocq
flocq/%.vo: COQCOPTS+=-w -compatibility-notation

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/extraction.v $(ARCH)/extractionMachdep.v
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/extraction.v
	touch extraction/STAMP

.depend.extr: extraction/STAMP tools/modorder driver/Version.ml
	$(MAKE) -f Makefile.extr depend

ccomp: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp
ccomp.byte: .depend.extr compcert.ini driver/Version.ml FORCE
	$(MAKE) -f Makefile.extr ccomp.byte

runtime:
	$(MAKE) -C runtime

FORCE:

.PHONY: proof extraction runtime FORCE

documentation: $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	coq2html -d doc/html/ -base compcert -short-names doc/*.glob \
          $(filter-out doc/coq2html cparser/Parser.v, $^)

tools/ndfun: tools/ndfun.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/ndfun str.cmxa tools/ndfun.ml
else
	ocamlc -o tools/ndfun str.cma tools/ndfun.ml
endif

tools/modorder: tools/modorder.ml
ifeq ($(OCAML_NATIVE_COMP),true)
	ocamlopt -o tools/modorder str.cmxa tools/modorder.ml
else
	ocamlc -o tools/modorder str.cma tools/modorder.ml
endif

latexdoc:
	cd doc; $(COQDOC) --latex -o doc/doc.tex -g $(FILES)

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

%.v: %.vp tools/ndfun
	@rm -f $*.v
	@echo "Preprocessing $*.vp"
	@tools/ndfun $*.vp > $*.v || { rm -f $*.v; exit 2; }
	@chmod a-w $*.v

compcert.ini: Makefile.config
	(echo "stdlib_path=$(LIBDIR)"; \
         echo "prepro=$(CPREPRO)"; \
         echo "linker=$(CLINKER)"; \
         echo "asm=$(CASM)"; \
	 echo "prepro_options=$(CPREPRO_OPTIONS)";\
	 echo "asm_options=$(CASM_OPTIONS)";\
	 echo "linker_options=$(CLINKER_OPTIONS)";\
         echo "arch=$(ARCH)"; \
         echo "model=$(MODEL)"; \
         echo "abi=$(ABI)"; \
         echo "endianness=$(ENDIANNESS)"; \
         echo "system=$(SYSTEM)"; \
         echo "has_runtime_lib=$(HAS_RUNTIME_LIB)"; \
         echo "has_standard_headers=$(HAS_STANDARD_HEADERS)"; \
         echo "asm_supports_cfi=$(ASM_SUPPORTS_CFI)"; \
	 echo "response_file_style=$(RESPONSEFILE)";) \
        > compcert.ini

compcert.config: Makefile.config
	(echo "# CompCert configuration parameters"; \
        echo "COMPCERT_ARCH=$(ARCH)"; \
        echo "COMPCERT_MODEL=$(MODEL)"; \
        echo "COMPCERT_ABI=$(ABI)"; \
        echo "COMPCERT_ENDIANNESS=$(ENDIANNESS)"; \
        echo "COMPCERT_BITSIZE=$(BITSIZE)"; \
        echo "COMPCERT_SYSTEM=$(SYSTEM)"; \
        echo "COMPCERT_VERSION=$(BUILDVERSION)"; \
        echo "COMPCERT_BUILDNR=$(BUILDNR)"; \
        echo "COMPCERT_TAG=$(TAG)"; \
        echo "COMPCERT_BRANCH=$(BRANCH)" \
        ) > compcert.config

driver/Version.ml: VERSION
	(echo 'let version = "$(BUILDVERSION)"'; \
         echo 'let buildnr = "$(BUILDNR)"'; \
         echo 'let tag = "$(TAG)"'; \
         echo 'let branch = "$(BRANCH)"') > driver/Version.ml

cparser/Parser.v: cparser/Parser.vy
	@rm -f $@
	$(MENHIR) --coq --coq-no-version-check cparser/Parser.vy
	@chmod a-w $@

depend: $(GENERATED) depend1

depend1: $(FILES) $(PROOFS)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

install:
	install -d $(DESTDIR)$(BINDIR)
	install -m 0755 ./ccomp $(DESTDIR)$(BINDIR)
	install -d $(DESTDIR)$(SHAREDIR)
	install -m 0644 ./compcert.ini $(DESTDIR)$(SHAREDIR)
	install -d $(DESTDIR)$(MANDIR)/man1
	install -m 0644 ./doc/ccomp.1 $(DESTDIR)$(MANDIR)/man1
	$(MAKE) -C runtime install
ifeq ($(INSTALL_COQDEV),true)
	install -d $(DESTDIR)$(COQDEVDIR)
	for d in $(DIRS); do \
          install -d $(DESTDIR)$(COQDEVDIR)/$$d && \
          install -m 0644 $$d/*.vo $(DESTDIR)$(COQDEVDIR)/$$d/; \
	done
	install -m 0644 ./VERSION $(DESTDIR)$(COQDEVDIR)
	install -m 0644 ./compcert.config $(DESTDIR)$(COQDEVDIR)
	@(echo "To use, pass the following to coq_makefile or add the following to _CoqProject:"; echo "-R $(COQDEVDIR) compcert") > $(DESTDIR)$(COQDEVDIR)/README
endif


clean:
	rm -f $(patsubst %, %/*.vo*, $(DIRS))
	rm -f $(patsubst %, %/.*.aux, $(DIRS))
	rm -rf doc/html doc/*.glob
	rm -f driver/Version.ml
	rm -f compcert.ini compcert.config
	rm -f extraction/STAMP extraction/*.ml extraction/*.mli .depend.extr
	rm -f tools/ndfun tools/modorder tools/*.cm? tools/*.o
	rm -f $(GENERATED) .depend
	rm -f .lia.cache
	$(MAKE) -f Makefile.extr clean
	$(MAKE) -C runtime clean
	$(MAKE) -C test clean

distclean:
	$(MAKE) clean
	rm -f Makefile.config

check-admitted: $(FILES)
	@grep -w 'admit\|Admitted\|ADMITTED' $^ || echo "Nothing admitted."

check-proof: $(FILES)
	$(COQCHK) compcert.driver.Complements

print-includes:
	@echo $(COQINCLUDES)

CoqProject:
	@echo $(COQINCLUDES) > _CoqProject

-include .depend

FORCE:
