# See LICENSE for licensing details.

OCB = ocamlbuild -classic-display

.PHONY: all
all:
	$(OCB) src/maetning.native

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