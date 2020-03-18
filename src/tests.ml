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

module type TESTER =
  functor (T : THEORY) ->
  sig
    val assert_equivalent : string -> string -> unit -> unit
    val assert_not_equivalent : string -> string -> unit -> unit
  end
 
module AutomataTester(T : THEORY) = struct
  module K = T.K
  module A = Automata(K)
           
  let assert_aux b s1 s2 () = 
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
           
  let assert_aux b s1 s2 () = 
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

(* Unit tests *)
module Unit (T : TESTER) = struct
  module Prod = Product(Addition)(Boolean)

  module TI = T(IncNat) 
  module TA = T(Addition)
  module TB = T(Boolean)
  module TP = T(Prod)

  (* TP.assert_equivalent 
      "y<1; (a=F + a=T; inc(y,1)); (b=F + b=T; inc(y,1)); (c=F + c=T; inc(y,1)); y>2"
      "a=T; b=T; c=T; inc(y,1); inc(y,1); inc(y,1)" *)
  
  let tests =
    ["Idempotency1" >::
       TA.assert_equivalent 
         "x > 2"  
         "x > 2";
     "Idempotency2" >::
       TA.assert_equivalent 
         "inc(x,1)*; x > 2"  
         "inc(x,1)*; x > 2";
     "Unrolling1" >::
       TA.assert_equivalent 
         "inc(x,1);inc(x,1)*; x > 2"
         "x>1;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2";
     "Unrolling2" >::
       TA.assert_equivalent 
         "inc(x,1)*; x > 2"  
         "x>2 + inc(x,1);inc(x,1)*; x > 2";
     "Unrolling3" >::
       TA.assert_equivalent 
         "inc(x,1)*; x > 2"  
         "x>2 + inc(x,1)*; x > 2";
     "Postcondition1" >::
       TA.assert_equivalent 
         "inc(x,1); inc(x,1); inc(x,1); x > 2"  
         "inc(x,1); inc(x,1); inc(x,1); x > 1"; 
     "Postcondition2" >::
       TA.assert_not_equivalent 
         "inc(x,1); inc(x,1); inc(x,1); x > 2"  
         "inc(x,1); inc(x,1); inc(x,1); x > 3";
     "Commutativity" >::
       TA.assert_equivalent 
         "inc(x,1);inc(y,1); x > 0; y > 0"
         "inc(x,1);inc(y,1); y > 0; x > 0";
     "Initial Conditions" >::
       TA.assert_not_equivalent 
         "inc(x,1);inc(x,1)*; x > 2"
         "x>2;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2";
     "Greater than" >::
       TA.assert_equivalent 
         "x>2;x>1"
         "x>2"; 
     "Commutativity-plus" >::
       TA.assert_equivalent
         "x > 2 + y > 1"
         "y > 1 + x > 2";
     "Idempotency-actions" >::
       TA.assert_equivalent
         "inc(x,1) + inc(x,1)"
         "inc(x,1)";
     "Test-in-loop1" >::
       TA.assert_equivalent
         "(inc(x,1);x>1)*"
         "true + x>0;inc(x,1);inc(x,1)*"; 
     "Test-in-loop2" >::
       TA.assert_not_equivalent
         "(inc(x,1);x>1)*"
         "true + inc(x,1);inc(x,1)*";
     "Idempotency1 (incnat)" >::
       TI.assert_equivalent 
         "x > 2"  
         "x > 2";
     "Idempotency2 (incnat)" >::
       TI.assert_equivalent 
         "inc(x)*; x > 2"  
         "inc(x)*; x > 2";
     "Unrolling1 (incnat)" >::
       TI.assert_equivalent 
         "inc(x);inc(x)*; x > 2"
         "x>1;inc(x) + inc(x);inc(x);inc(x)*; x > 2";
     "Unrolling2 (incnat)" >::
       TI.assert_equivalent 
         "inc(x)*; x > 2"  
         "x>2 + inc(x);inc(x)*; x > 2";
     "Unrolling3 (incnat)" >::
       TI.assert_equivalent 
         "inc(x)*; x > 2"  
         "x>2 + inc(x)*; x > 2";
     "Postcondition1 (incnat)" >::
       TI.assert_equivalent 
         "inc(x); inc(x); inc(x); x > 2"  
         "inc(x); inc(x); inc(x); x > 1"; 
     "Postcondition2 (incnat)" >::
       TI.assert_not_equivalent 
         "inc(x); inc(x); inc(x); x > 2"  
         "inc(x); inc(x); inc(x); x > 3";
     "Commutativity (incnat)" >::
       TI.assert_equivalent 
         "inc(x);inc(y); x > 0; y > 0"
         "inc(x);inc(y); y > 0; x > 0";
     "Initial Conditions (incnat)" >::
       TI.assert_not_equivalent 
         "inc(x);inc(x)*; x > 2"
         "x>2;inc(x) + inc(x);inc(x);inc(x)*; x > 2";
     "Greater than (incnat)" >::
       TI.assert_equivalent 
         "x>2;x>1"
         "x>2";
     "Commutativity-plus (incnat)" >::
       TI.assert_equivalent
         "x > 2 + y > 1"
         "y > 1 + x > 2";
     "Idempotency-actions (incnat)" >::
       TI.assert_equivalent
         "inc(x) + inc(x)"
         "inc(x)";
     "Test-in-loop1 (incnat)" >::
       TI.assert_equivalent
         "(inc(x);x>1)*"
         "true + x>0;inc(x);inc(x)*"; 
     "Test-in-loop2 (incnat)" >::
       TI.assert_not_equivalent
         "(inc(x);x>1)*"
         "true + inc(x);inc(x)*";
     "Canceled-set (incnat)" >::
       TI.assert_equivalent
         "set(x,0);x>0"
         "false";
     "Set-canceled-pred (incnat)" >::
       TI.assert_equivalent
         "set(x,5);x>0"
         "set(x,5)";
     "Tracing (incnat)" >::
       TI.assert_not_equivalent
         "(inc(x))*;set(x,0)"
         "set(x,0)";
     "Boolean-assign-eq" >::
       TB.assert_equivalent
         "set(x,T); x=T"
         "set(x,T)";
     "Boolean-assign-neq" >::
       TB.assert_not_equivalent
         "set(x,T); x=F"
         "set(x,T)";
     "Boolean-assign-eq2" >::
       TB.assert_equivalent
         "set(x,T); set(x,F); x=F"
         "set(x,T); set(x,F)";
     (* taking too long in normalization... *)     
(*     "Boolean-parity-loop" >::
       TB.assert_equivalent
         "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*"
         "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=F";
     "Boolean-parity-loop2" >::
       TB.assert_not_equivalent
         "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*"
         "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=T"; *)
     "Boolean-finiteness" >::
       TB.assert_equivalent
         "x=F + x=T"
         "true";
     "Boolean-associativity" >::
       TB.assert_equivalent
         "(x=F + y=F) + z=F"
         "x=F + (y=F + z=F)";
     "Boolean-multiple-vars" >::
       TB.assert_equivalent
         "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=T + x=F;y=F)"
         "(x=T; set(y,T) + x=F; set(y,F))";
     "Boolean-multiple-vars2" >::
       TB.assert_not_equivalent
         "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=F + x=F;y=F)"
         "(x=T; set(y,T) + x=F; set(y,F))";
     "Boolean-tree-ordering" >::
       (let s1 = "set(w,F); set(x,T); set(y,F); set(z,F); ((w=T + x=T + y=T + z=T); set(a,T) + (not (w=T + x=T + y=T + z=T)); set(a,F))" in
        let s2 = "set(w,F); set(x,T); set(y,F); set(z,F); (((w=T + x=T) + (y=T + z=T)); set(a,T) + (not ((w=T + x=T) + (y=T + z=T))); set(a,F))" in
        TB.assert_equivalent s1 s2);
    "Product-parsing" >::
      TP.assert_equivalent
        "set(x,T); x=T; inc(y,1)"
        "set(x,T); inc(y,1)";
    "Product-action-ordering" >::
      TP.assert_not_equivalent
        "set(x,T); inc(y,1)"
        "inc(y,1); set(x,T)";
    "Product-population-count" >::
      TP.assert_equivalent 
        "y<1; (a=F + a=T; inc(y,1)); y > 0"
        "y<1; a=T; inc(y,1)";
    "Product-population-count2" >::
      TP.assert_not_equivalent 
        "y<1; (a=F + a=T; inc(y,1))"
        "a=T; inc(y,1)";
    "KAT P* identity" >::
          TB.assert_equivalent
      "(a=T)*"
      "(a=T;a=T)* + a=T;(a=T;a=T)*"
    ]

end

module NormalizeTests = Unit(NormalizationTester)
module AutomataTests = Unit(AutomataTester)                      

let check tests =
  let pairs = List.mapi (fun i (n,test) -> (n, String.length (string_of_int i ^ " " ^ n), test)) tests in
  let sizes = List.map (fun (_,sz,_) -> sz) pairs in
  let max_len = (List.fold_left max 0 sizes) + 5 in
  let results = List.map (fun (n,sz,res) -> (n,max_len-sz,res)) pairs in
  let failures = ref 0 in
  T.print_string [] "==========================================\n";
  List.iteri (fun i (name,spaces,test) ->
    T.printf [] "%d %s%s" i name (Common.repeat spaces " "); flush stdout;
    flush stdout;
    match run test with 
    | Success ->
       T.print_string [T.Foreground T.Green] "[Success]\n";
       flush stdout
    | Failure(s1,s2) ->
       incr failures;
       T.print_string [T.Foreground T.Red] "[Failed]\n\n";
       T.print_string [T.Foreground T.Yellow] (s1 ^ "\n");
       T.print_string [T.Foreground T.Yellow] (s2 ^ "\n\n");
       flush stdout
    ) results;
  let total = List.length tests in
  T.print_string [] "==========================================\n";
  T.printf [T.Bold] "%d/%d passed\n" (total - !failures) total;
  T.print_string [] "==========================================\n"
                     
let main () =
  T.print_string [T.Bold; T.Foreground T.Blue ] "Normalization tests\n";
  check NormalizeTests.tests;
  T.print_string [] "\n\n";
  T.print_string [] "==========================================\n";
  T.print_string [T.Bold; T.Foreground T.Blue ] "Automata tests\n";
  check AutomataTests.tests
;;

main ()
