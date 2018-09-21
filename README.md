An implementation of [Kleene algebra modulo theories](https://arxiv.org/abs/1707.02894) (KMT), a framework for composing and deriving programming languages with sound and complete decision procedures for program equivalence.

# How do I build it?

If you have a recent version of OCaml, simply typing `make` should do the trick---it will call `ocamlbuild` for you. `make eval` will reproduce the evaluation from our paper; `make test` runs regression tests.

You'll need the following OCaml packages: `ppx_deriving`, `batteries`, `ANSIterminal`, and `z3`. The build is via `ocamlbuild`.

# Which example should I look at first?

Check out `src/incnat.ml` for a simple language with increment and assignment operations. It defines types `a` and `p` for the primitive parts of the language (one predicate, which tests whether a variable is greater than a number, and two actions, which increment and set variables).

The code in `src/bool.ml` is for a simple language with boolean-valued variables.

The code in `src/ltlf.ml` is for a _higher-order theory_, wrapping a given theory with predicates for testing LTLf (past-time finite linear temporal logic) predicates.

# What is KMT?

Kleene algebra modulo theories (KMT) is a framework for deriving _concrete_ Kleene algebras with tests (KATs), an algebraic framework for While-like programs with decidable program equivalence.

More plainly: KMT is a framework for building simple programming languages with structure control (if, while, etc.) where you we can decide whether or not two programs are equivalent. You can use equivalence to verify programs (if `a` is a nice property to have after running your program, then if `p;a == p`, you know that `p` satisfies `a`; if `a;p;~b == 0` then all runs starting from `a` either diverge or end with `b`,).

# What do I have to provide?

The source code in `src/incnat.ml` is a nice example. You have to provide:

- sub-modules `P` and `A` for the primitive parts of your language
- a `parse` function to indicate how to parse the syntax of your primitives
- a `push_back` operation that calculates weakest preconditions on a pair of a primitive and a predicate
- a `subterms` function that captures which predicates could show up in `push_back` of a given predicate
- a `satisfiable` function to test whether a predicate is satisfiable

To use the Z3 backend, your theory can describe how it extracts to Z3 using functions `variable`, `variable_test`, `create_z3_var`, and `theory_to_z3_expr`.

Note that `incnat.ml`'s theory solver in `satisfiable` has two cases: a fast path that need not use Z3, and a more general decision procedure in Z3.

# How is equivalence decided?

We offer two forms of equivalence: one via normalization and on via automata.

When we use normalization to check equivalence, we rewrite the two programs under comparison into a normal form and compare them. When this procedure is fast, it's _quite_ fast... but deeply nested loops or loops with lots of conditionals slow it down severely.

The automata equivalence procedure translates programs into finite automata, for which we can use symbolic methods to decide equivalence. While it's not typically as fast as the normalization routine, it doesn't exhibit any particularly pathological cases.
