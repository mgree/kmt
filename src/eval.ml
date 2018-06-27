open Kat
open Addition
open Automata

module T = ANSITerminal
module K = Addition.K
module A = Automata(K)

let variables = ["a"; "b"; "c"; "d"; "e"; "f"; "g"]

let random_addition_theory (vars : int) (bound : int) = 
  let v = Random.int vars in
  let b = Random.int bound in
  let dir = Random.int 2 in
  let str = List.nth variables v in 
  if (dir = 0) then Lt (str, b) else Gt (str, b) 

let random_addition_action (vars : int) (bound : int) = 
  let v = Random.int vars in
  let b = Random.int bound in
  let str = string_of_int v in 
  Increment (str, b)

module Random (K : KAT_IMPL) = struct 

  let split sz = 
    let x = Random.int (sz + 1) in 
    if (x = 0) then (1, sz - 1)
    else if (x = sz) then (sz - 1, 1) else 
    (x, sz - x)

  let rec random_test (size : int) (f : unit -> K.A.t) : K.Test.t = 
    if size = 1 then K.theory (f ()) else
    let x = Random.int 5 in 
    let (l,r) = split size in
    if (x < 1) then K.not (random_test (size - 1) f) else
    if (x < 3) then K.ppar (random_test l f) (random_test r f) else 
    K.pseq (random_test l f) (random_test r f) 

  let rec random_term (size : int) (f : unit -> K.P.t) : K.Term.t = 
    if size = 1 then K.action (f ()) else
    let x = Random.int 5 in 
    let (l,r) = split size in
    if (x < 2) then K.par (random_term l f) (random_term r f) else 
    if (x < 4) then K.seq (random_term l f) (random_term r f) else 
    K.star (random_term (size - 1) f)

end

module R = Random(K)

let test_astar_a test = 
  let term1 = K.pred test in 
  let term2 = K.star term1 in
  let auto1 = A.of_term term1 in
  let auto2 = A.of_term term2 in
  let eq = A.equivalent auto1 auto2 in 
  assert (not eq);
  ()

let main = 
  let test1 = R.random_test 10 (fun () -> random_addition_theory 2 3) in 
  let test2 = R.random_test 100 (fun () -> random_addition_theory 2 3) in 
  let (_, t1) = Common.time test_astar_a test1 in
  let (_, t2) = Common.time test_astar_a test2 in
  Printf.printf "a* != a (10)      [time: %f]\n" t1;
  Printf.printf "a* != a (100)     [time: %f]\n" t2;
  ()