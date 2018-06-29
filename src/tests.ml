open Kat
open Addition
open Boolean
open Automata

module T = ANSITerminal

exception Violation of string * string

type result = 
  | Success 
  | Failure of string * string

module Tester(K : KAT_IMPL) = struct 
  module A = Automata(K)

  let assert_aux b s1 s2 = 
    let x = K.parse s1 in 
    let y = K.parse s2 in 
    let a1 = A.of_term x in 
    let a2 = A.of_term y in 
    let equiv = A.equivalent a1 a2 in
    if (b && not equiv) || (not b && equiv)  then 
      raise (Violation (s1,s2))

  let assert_equivalent = assert_aux true
  let assert_not_equivalent = assert_aux false
end

let (>::) x y = (x,y)
let (%) f g = fun x -> g (f x)

let run test = 
  try 
    test ();
    Success 
  with Violation(s1,s2) -> Failure(s1,s2) 


let check tests =
  let pairs = List.map (fun (n,test) -> (n, String.length n, test)) tests in
  let sizes = List.map (fun (_,sz,_) -> sz) pairs in
  let max_len = (List.fold_left max 0 sizes) + 5 in
  let results = List.map (fun (n,sz,res) -> (n,max_len-sz,res)) pairs in
  T.print_string [] "=============================\n";
  List.iter (fun (name,spaces,test) -> 
    match run test with 
    | Success ->
        T.print_string [] name;
        T.print_string [] (Common.repeat spaces " ");
        T.print_string [T.Foreground T.Green] "[Success]\n"
    | Failure(s1,s2) -> 
        T.print_string [] name;
        T.print_string [] (Common.repeat spaces " ");
        T.print_string [T.Foreground T.Red] "[Failed]\n\n";
        T.print_string [T.Foreground T.Black] (s1 ^ "\n");
        T.print_string [T.Foreground T.Black] (s2 ^ "\n\n");
  ) results;
  T.print_string [] "=============================\n"


(* Unit tests *)
module Unit = struct

  module TA = Tester(Addition.K)
  module TB = Tester(Boolean.K)

  let test0 () = 
    TA.assert_equivalent 
      "x > 2"  
      "x > 2"

  let test1 () = 
    TA.assert_equivalent 
      "inc(x,1)*; x > 2"  
      "inc(x,1)*; x > 2"

  let test2 () = 
    TA.assert_equivalent 
      "inc(x,1);inc(x,1)*; x > 2"
      "x>1;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2"

  let test3 () = 
    TA.assert_equivalent 
      "inc(x,1)*; x > 2"  
      "x>2 + inc(x,1);inc(x,1)*; x > 2"

  let test4 () = 
    TA.assert_equivalent 
      "inc(x,1); inc(x,1); inc(x,1); x > 2"  
      "inc(x,1); inc(x,1); inc(x,1); x > 1"

  let test5 () = 
    TA.assert_not_equivalent 
      "inc(x,1); inc(x,1); inc(x,1); x > 2"  
      "inc(x,1); inc(x,1); inc(x,1); x > 3"
   
  let test6 () = 
    TA.assert_equivalent 
      "inc(x,1);inc(y,1); x > 0; y > 0"
      "inc(x,1);inc(y,1); y > 0; x > 0"

  let test7 () = 
    TA.assert_not_equivalent 
      "inc(x,1);inc(x,1)*; x > 2"
      "x>2;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2"

  let test8 () = 
    TA.assert_equivalent 
      "x>2;x>1"
      "x>2"

  let test9 () = 
    TA.assert_equivalent
      "x > 2 + y > 1"
      "y > 1 + x > 2"

  let test10 () = 
    TA.assert_equivalent
      "inc(x,1) + inc(x,1)"
      "inc(x,1)"

  let test11 () = 
    TA.assert_equivalent
      "(inc(x,1);x>1)*"
      "true + x>0;inc(x,1);inc(x,1)*"

  let test12 () = 
    TA.assert_not_equivalent
      "(inc(x,1);x>1)*"
      "true + inc(x,1);inc(x,1)*"

  let test13 () = 
    TB.assert_equivalent
      "set(x,T); x=T"
      "set(x,T)"

  let test14 () = 
    TB.assert_not_equivalent
      "set(x,T); x=F"
      "set(x,T)"

  let test15 () = 
    TB.assert_equivalent
      "set(x,T); set(x,F); x=F"
      "set(x,T); set(x,F)"

  let test16 () = 
    TB.assert_equivalent
      "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*"
      "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=F"

  let test17 () = 
    TB.assert_not_equivalent
      "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*"
      "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=T"

  let test18 () = 
    TB.assert_equivalent
      "x=F + x=T"
      "true"

  let test19 () = 
    TB.assert_equivalent
      "(x=F + y=F) + z=F"
      "x=F + (y=F + z=F)"

  let test20 () = 
    TB.assert_equivalent
      "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=T + x=F;y=F)"
      "(x=T; set(y,T) + x=F; set(y,F))"

  let test21 () = 
    TB.assert_equivalent
      "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=F + x=F;y=F)"
      "(x=T; set(y,T) + x=F; set(y,F))"

  let tests = 
    ["Idempotency1" >:: test0;
     "Idempotency2" >:: test1;
     "Unrolling1" >:: test2;
     "Unrolling2" >:: test3;
     "Postcondition1" >:: test4; 
     "Postcondition2" >:: test5;
     "Commutativity" >:: test6;
     "Initial Conditions" >:: test7;
     "Greater than" >:: test8; 
     "Commutativity-plus" >:: test9;
     "Idempotency-actions" >:: test10;
     "Test-in-loop1" >:: test11; 
     "Test-in-loop2" >:: test12;
     "Boolean-assign-eq" >:: test13;
     "Boolean-assign-neq" >:: test14;
     "Boolean-assign-eq2" >:: test15;
     "Boolean-parity-loop" >:: test16;
     "Boolean-parity-loop2" >:: test17;
     "Boolean-finiteness" >:: test18;
     "Boolean-associativity" >:: test19;
     "Boolean-multiple-vars" >:: test20]

end;;

check Unit.tests