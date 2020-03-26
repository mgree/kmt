MLFILES=src/*.ml src/*.mli src/*.mll src/*.mly

build: main.native

test: test_equivalence test_word

test_equivalence : src/test_equivalence.ml
	$(MAKE) test_equivalence.native
	./test_equivalence.native

test_word : src/test_word.ml
	$(MAKE) test_word.native
	./test_word.native

eval: src/eval.ml
	$(MAKE) eval.native
	./eval.native

%.native: $(MLFILES)
	ocamlbuild -use-ocamlfind -r src/$@

clean:
	ocamlbuild -clean
	rm -f bin/*.native

.PHONY: build run test test_equivalence test_word clean
