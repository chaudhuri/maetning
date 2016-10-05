# See LICENSE for licensing details.

OCB = ocamlbuild -classic-display

.PHONY: all
all: maetning.native formgen.native

%.native: $(wildcard src/*.ml*)
	$(OCB) src/$@

.PHONY: clean
clean:
	$(OCB) -clean
	$(RM) src/version.ml
	$(RM) maetning maetning.exe

.PHONY: byte
byte:
	$(OCB) src/maetning.byte

.PHONY: gitclean
gitclean:
	git clean -xfd -e examples

.PHONY: top
top: all
	$(OCB) src/maetning.cma
	ocaml
