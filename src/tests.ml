open Kat
open Incnat
open Addition
open Boolean
open Product
open Automata
open Decide
   
module T = ANSITerminal

exception Violation of string * string

type result = 
  | Success 
  | Failure of string * string
             
module AutomataTester(T : THEORY) = struct
  module K = T.K
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

module NormalizationTester(T : THEORY) = struct
  module K = T.K
  module D = Decide(T)
           
  let assert_aux b s1 s2 = 
    let p = K.parse s1 in 
    let q = K.parse s2 in 
    let equiv = D.equivalent p q in
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
  T.print_string [] "==========================================\n";
  List.iter (fun (name,spaces,test) ->
    T.print_string [] name;
    T.print_string [] (Common.repeat spaces " "); flush stdout;
    flush stdout;
    match run test with 
    | Success ->
        T.print_string [T.Foreground T.Green] "[Success]\n";
        flush stdout
    | Failure(s1,s2) -> 
        T.print_string [T.Foreground T.Red] "[Failed]\n\n";
        T.print_string [T.Foreground T.Black] (s1 ^ "\n");
        T.print_string [T.Foreground T.Black] (s2 ^ "\n\n");
        flush stdout
  ) results;
  T.print_string [] "==========================================\n";


(* Unit tests *)
module Unit = struct
  module Prod = Product(Addition)(Boolean)

  module TI = AutomataTester(IncNat) 
  module TA = AutomataTester(Addition)
  module TB = AutomataTester(Boolean)
  module TP = AutomataTester(Prod)

  let test0 () = 
    TA.assert_equivalent 
      "x > 2"  
      "x > 2"

  let test0_incnat () = 
    TI.assert_equivalent 
      "x > 2"  
      "x > 2"    

  let test1 () = 
    TA.assert_equivalent 
      "inc(x,1)*; x > 2"  
      "inc(x,1)*; x > 2"

  let test1_incnat () = 
    TI.assert_equivalent 
      "inc(x)*; x > 2"  
      "inc(x)*; x > 2"

  let test2 () = 
    TA.assert_equivalent 
      "inc(x,1);inc(x,1)*; x > 2"
      "x>1;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2"

  let test2_incnat () = 
    TI.assert_equivalent 
      "inc(x);inc(x)*; x > 2"
      "x>1;inc(x) + inc(x);inc(x);inc(x)*; x > 2"
    
  let test3 () = 
    TA.assert_equivalent 
      "inc(x,1)*; x > 2"  
      "x>2 + inc(x,1);inc(x,1)*; x > 2"

  let test3_incnat () = 
    TI.assert_equivalent 
      "inc(x)*; x > 2"  
      "x>2 + inc(x);inc(x)*; x > 2"
    
  let test4 () = 
    TA.assert_equivalent 
      "inc(x,1); inc(x,1); inc(x,1); x > 2"  
      "inc(x,1); inc(x,1); inc(x,1); x > 1"

  let test4_incnat () = 
    TI.assert_equivalent 
      "inc(x); inc(x); inc(x); x > 2"  
      "inc(x); inc(x); inc(x); x > 1"

  let test5 () = 
    TA.assert_not_equivalent 
      "inc(x,1); inc(x,1); inc(x,1); x > 2"  
      "inc(x,1); inc(x,1); inc(x,1); x > 3"

  let test5_incnat () = 
    TI.assert_not_equivalent 
      "inc(x); inc(x); inc(x); x > 2"  
      "inc(x); inc(x); inc(x); x > 3"
    
  let test6 () = 
    TA.assert_equivalent 
      "inc(x,1);inc(y,1); x > 0; y > 0"
      "inc(x,1);inc(y,1); y > 0; x > 0"

  let test6_incnat () = 
    TI.assert_equivalent 
      "inc(x);inc(y); x > 0; y > 0"
      "inc(x);inc(y); y > 0; x > 0"
    
  let test7 () = 
    TA.assert_not_equivalent 
      "inc(x,1);inc(x,1)*; x > 2"
      "x>2;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2"

  let test7_incnat () = 
    TI.assert_not_equivalent 
      "inc(x);inc(x)*; x > 2"
      "x>2;inc(x) + inc(x);inc(x);inc(x)*; x > 2"
    
  let test8 () = 
    TA.assert_equivalent 
      "x>2;x>1"
      "x>2"

  let test8_incnat () = 
    TI.assert_equivalent 
      "x>2;x>1"
      "x>2"
    
  let test9 () = 
    TA.assert_equivalent
      "x > 2 + y > 1"
      "y > 1 + x > 2"

  let test9_incnat () = 
    TI.assert_equivalent
      "x > 2 + y > 1"
      "y > 1 + x > 2"
    
  let test10 () = 
    TA.assert_equivalent
      "inc(x,1) + inc(x,1)"
      "inc(x,1)"

  let test10_incnat () = 
    TI.assert_equivalent
      "inc(x) + inc(x)"
      "inc(x)"
    
  let test11 () = 
    TA.assert_equivalent
      "(inc(x,1);x>1)*"
      "true + x>0;inc(x,1);inc(x,1)*"

  let test11_incnat () = 
    TI.assert_equivalent
      "(inc(x);x>1)*"
      "true + x>0;inc(x);inc(x)*"
    
  let test12 () = 
    TA.assert_not_equivalent
      "(inc(x,1);x>1)*"
      "true + inc(x,1);inc(x,1)*"

  let test12_incnat () = 
    TI.assert_not_equivalent
      "(inc(x);x>1)*"
      "true + inc(x);inc(x)*"

  let test13_incnat () =
    TI.assert_equivalent
      "set(x,0);x>0"
      "false"

  let test14_incnat () =
    TI.assert_equivalent
      "set(x,5);x>0"
      "set(x,5)"

  let test15_incnat () =
    TI.assert_not_equivalent
      "(inc(x))*;set(x,0)"
      "set(x,0)"
    
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
    TB.assert_not_equivalent
      "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=F + x=F;y=F)"
      "(x=T; set(y,T) + x=F; set(y,F))"

  let test22 () = 
    let s1 = "set(w,F); set(x,T); set(y,F); set(z,F); ((w=T + x=T + y=T + z=T); set(a,T) + (not (w=T + x=T + y=T + z=T)); set(a,F))" in
    let s2 = "set(w,F); set(x,T); set(y,F); set(z,F); (((w=T + x=T) + (y=T + z=T)); set(a,T) + (not ((w=T + x=T) + (y=T + z=T))); set(a,F))" in
    TB.assert_equivalent s1 s2

  let test23 () = 
    TP.assert_equivalent
      "set(x,T); x=T; inc(y,1)"
      "set(x,T); inc(y,1)"
  
  let test24 () = 
    TP.assert_not_equivalent
      "set(x,T); inc(y,1)"
      "inc(y,1); set(x,T)"

  (* let test25 () = 
    TP.assert_equivalent 
      "y<1; (a=F + a=T; inc(y,1)); (b=F + b=T; inc(y,1)); (c=F + c=T; inc(y,1)); y>2"
      "a=T; b=T; c=T; inc(y,1); inc(y,1); inc(y,1)" *)

  let test25 () = 
    TP.assert_equivalent 
      "y<1; (a=F + a=T; inc(y,1)); y > 0"
      "a=T; inc(y,1)"

  let test26 () = 
    TP.assert_not_equivalent 
      "y<1; (a=F + a=T; inc(y,1))"
      "a=T; inc(y,1)"

  let test27 () = 
    TB.assert_equivalent
      "(a=T)*"
      "(a=T;a=T)* + a=T;(a=T;a=T)*"
  
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
     "Idempotency1 (incnat)" >:: test0_incnat;
     "Idempotency2 (incnat)" >:: test1_incnat;
     "Unrolling1 (incnat)" >:: test2_incnat;
     "Unrolling2 (incnat)" >:: test3_incnat;
     "Postcondition1 (incnat)" >:: test4_incnat; 
     "Postcondition2 (incnat)" >:: test5_incnat;
     "Commutativity (incnat)" >:: test6_incnat;
     "Initial Conditions (incnat)" >:: test7_incnat;
     "Greater than (incnat)" >:: test8_incnat;
     "Commutativity-plus (incnat)" >:: test9_incnat;
     "Idempotency-actions (incnat)" >:: test10_incnat;
     "Test-in-loop1 (incnat)" >:: test11_incnat; 
     "Test-in-loop2 (incnat)" >:: test12_incnat;
     "Canceled-set (incnat)" >:: test13_incnat;
     "Set-canceled-pred (incnat)" >:: test14_incnat;
     "Tracing (incnat)" >:: test15_incnat;
     "Boolean-assign-eq" >:: test13;
     "Boolean-assign-neq" >:: test14;
     "Boolean-assign-eq2" >:: test15;
     "Boolean-parity-loop" >:: test16;
     "Boolean-parity-loop2" >:: test17;
     "Boolean-finiteness" >:: test18;
     "Boolean-associativity" >:: test19;
     "Boolean-multiple-vars" >:: test20;
     "Boolean-multiple-vars2" >:: test21;
     "Boolean-tree-ordering" >:: test22;
     "Product-parsing" >:: test23;
     "Product-action-ordering" >:: test24;
     "Product-population-count" >:: test25;
     "Product-population-count2" >:: test26;
     "KAT P* identity" >:: test27]

end;;

check Unit.tests
