build:
	dune build -- src/kmt

test: test_equivalence test_word

test_equivalence: 
	dune exec -- src/test_equivalence

test_word:
	dune exec -- src/test_word

eval:
	dune exec -- src/eval

clean:
	dune clean

.PHONY: build run test test_equivalence test_word eval clean
