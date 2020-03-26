MLFILES= src/*.ml src/*.mli src/*.mll src/*.mly

build: main.native

run: build
	./main.native

test: src/test_equivalence.ml 
	$(MAKE) test_equivalence.native
	./test_equivalence.native

eval: src/eval.ml
	$(MAKE) eval.native
	./eval.native

%.native: $(MLFILES)
	ocamlbuild -use-ocamlfind -r src/$@

clean:
	ocamlbuild -clean
	rm -f bin/*.native

.PHONY: build clean
