MLFILES= src/*.ml src/*.mli src/*.mll src/*.mly

build: main.native

%.native: $(MLFILES)
	ocamlbuild -use-ocamlfind -r src/$@

run: build
	./main.native

test: src/tests.ml 
	ocamlbuild -use-ocamlfind -r src/tests.native
	./tests.native

eval: src/eval.ml
	ocamlbuild -use-ocamlfind -r src/eval.native
	./eval.native

clean:
	ocamlbuild -clean
	rm -f bin/*.native

.PHONY: build clean
