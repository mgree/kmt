open Kat
open Addition
open Boolean
open Product
open Automata

module T = ANSITerminal
module KA = Addition.K
module KB = Boolean.K
module Prod = Product(Addition)(Boolean)
module KP = Prod.K
module AA = Automata(KA)
module AB = Automata(KB)

let variables = ["a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"]

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

module RA = Random(KA)

let test_astar_a test = 
  let term1 = KA.pred test in 
  let term2 = KA.star term1 in
  let auto1 = AA.of_term term1 in
  let auto2 = AA.of_term term2 in
  let eq = AA.equivalent auto1 auto2 in 
  assert (not eq);
  ()

let test_count_twice () = 
  let term1 = KA.parse "(inc(x,1))*; x > 10" in
  let term2 = KA.parse "(inc(x,1))*;(inc(x,1))*; x > 10" in 
  let auto1 = AA.of_term term1 in 
  let auto2 = AA.of_term term2 in 
  let eq = AA.equivalent auto1 auto2 in 
  assert eq;
  ()

let test_count_order () = 
  let term1 = KA.parse "(inc(x,1))*; x > 3; (inc(y,1))*; y > 3" in
  let term2 = KA.parse "(inc(x,1))*; (inc(y,1))*; x > 3; y > 3" in 
  let auto1 = AA.of_term term1 in 
  let auto2 = AA.of_term term2 in 
  let eq = AA.equivalent auto1 auto2 in 
  assert eq;
  ()

let test_parity_loop () = 
  let term1 = KB.parse "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*" in 
  let term2 = KB.parse "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=F" in 
  let auto1 = AB.of_term term1 in 
  let auto2 = AB.of_term term2 in 
  let eq = AB.equivalent auto1 auto2 in 
  assert eq;
  ()


let test_boolean_formula () = 
  let term1 = KB.parse "set(w,F); set(x,T); set(y,F); set(z,F); ((w=T + x=T + y=T + z=T); set(a,T) + (not (w=T + x=T + y=T + z=T)); set(a,F))" in
  let term2 = KB.parse "set(w,F); set(x,T); set(y,F); set(z,F); (((w=T + x=T) + (y=T + z=T)); set(a,T) + (not ((w=T + x=T) + (y=T + z=T))); set(a,F))" in
  let auto1 = AB.of_term term1 in 
  let auto2 = AB.of_term term2 in 
  let eq = AB.equivalent auto1 auto2 in 
  assert eq;
  ()


let main = 
  let test1 = RA.random_test 10 (fun () -> random_addition_theory 2 3) in 
  (* let test2 = RA.random_test 100 (fun () -> random_addition_theory 2 3) in *)
  let (_, t1) = Common.time test_astar_a test1 in
  (* let (_, t2) = Common.time test_astar_a test2 in *)
  let (_, t3) = Common.time test_count_twice () in 
  let (_, t4) = Common.time test_count_order () in
  let (_, t5) = Common.time test_parity_loop () in
  let (_, t6) = Common.time test_boolean_formula () in


  Printf.printf "a* != a (10)      [time: %f]\n" t1;
  (* Printf.printf "a* != a (100)     [time: %f]\n" t2; *) 
  Printf.printf "count twice       [time: %f]\n" t3;
  Printf.printf "count order       [time: %f]\n" t4;
  Printf.printf "parity loop       [time: %f]\n" t5;
  Printf.printf "boolean tree      [time: %f]\n" t6