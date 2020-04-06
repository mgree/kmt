- Logging
  + Tagging of topics (e.g., sat, other stuff...)

- Change normalization routine to use minterms

- SMT module
- Commonality in `satisfiable`?

- fancy OCaml modules to dynamically generate KMT theories?
  (can you define a recursive function with a module return type?)

- Testing
  + Frontend
  + Bring automata and normalization in line
    * Property-based testing
    * Option to use `same_actions_automata` in decide.ml
  + Fix eval to be nicer

- Use Fmt for better pretty printing
- Switch to dune-based build?
- Break off word stuff as a separate library?
- OPAM package?

- Heuristic optimizations
  + `p*p` ~~> `pp*`
  + "normal" order for +?
  + x>3; not (x > 2) ~~> 0
