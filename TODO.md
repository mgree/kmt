- lanf -> lunf

- Logging
  + Tagging of topics (e.g., sat, other stuff...)

- Commonality in `satisfiable`?

- Testing
  + Negative examples of word equality
  + Frontends
  + Bring automata and normalization in line
    * Property-based testing
    * Scour old thread for example of where automata is failing
    * Option to use `same_actions_automata` in decide.ml


- Use Fmt for better pretty printing
- Switch to dune-based build?
- Break off word stuff as a separate library?
- OPAM package?


- Heuristic optimizations
  + `p*p` ~~> `pp*`
  + "normal" order for +?
  + x>3; not (x > 2) ~~> 0
