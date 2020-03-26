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
    type t = string

    val pp : t Fmt.t

    val equal : t -> t -> bool
    
    val assert_equivalent : string -> string -> string -> unit Alcotest.test_case
    val assert_not_equivalent : string -> string -> string -> unit Alcotest.test_case
  end

module AutomataTester(T : THEORY) = struct
  module K = T.K
  module A = Automata(K)

  type t = string

  let pp fmt x = Fmt.pf fmt "%s" x
         
  let equal s1 s2 =          
    let x = K.parse s1 in 
    let y = K.parse s2 in 
    let a1 = A.of_term x in 
    let a2 = A.of_term y in 
    A.equivalent a1 a2

  let equivalent : string Alcotest.testable = Alcotest.testable pp equal

  let assert_equivalent name l r =
    Alcotest.test_case name `Quick (fun () -> Alcotest.(check equivalent) "equivalent" l r)
  let assert_not_equivalent name l r =
    Alcotest.test_case name `Quick (fun () -> Alcotest.(check (Alcotest.neg equivalent)) "inequivalent" l r)
end

module NormalizationTester(T : THEORY) = struct
  module K = T.K
  module D = Decide(T)

  type t = string

  let pp fmt x = Fmt.pf fmt "%s" x

  let equal s1 s2 =         
    let p = K.parse s1 in 
    let q = K.parse s2 in 
    D.equivalent p q
    
  let equivalent : string Alcotest.testable = Alcotest.testable pp equal

  let assert_equivalent name l r =
    Alcotest.test_case name `Quick (fun () -> Alcotest.(check equivalent) "equivalent" l r)
  let assert_not_equivalent name l r =
    Alcotest.test_case name `Quick (fun () -> Alcotest.(check (Alcotest.neg equivalent)) "inequivalent" l r)
end

let (%) f g = fun x -> g (f x)

let run test = 
  try 
    test ();
    Success 
  with Violation(s1,s2) -> Failure(s1,s2) 

(* Unit tests *)
module TestAddition (T : TESTER) = struct
  module TA = T(Addition)
  open TA

  let tests =
    [ assert_equivalent "Idempotency1"  
         "x > 2"  
         "x > 2";
      assert_equivalent "Idempotency2"  
         "inc(x,1)*; x > 2"  
         "inc(x,1)*; x > 2";
      assert_equivalent "Unrolling1"  
         "inc(x,1);inc(x,1)*; x > 2"
         "x>1;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2";
      assert_equivalent "Unrolling2"  
         "inc(x,1)*; x > 2"  
         "x>2 + inc(x,1);inc(x,1)*; x > 2";
      assert_equivalent "Unrolling3"  
         "inc(x,1)*; x > 2"  
         "x>2 + inc(x,1)*; x > 2";
      assert_equivalent "Postcondition1"  
         "inc(x,1); inc(x,1); inc(x,1); x > 2"  
         "inc(x,1); inc(x,1); inc(x,1); x > 1"; 
      assert_not_equivalent "Postcondition2"  
         "inc(x,1); inc(x,1); inc(x,1); x > 2"  
         "inc(x,1); inc(x,1); inc(x,1); x > 3";
      assert_equivalent "Commutativity"  
         "inc(x,1);inc(y,1); x > 0; y > 0"
         "inc(x,1);inc(y,1); y > 0; x > 0";
      assert_not_equivalent "Initial Conditions"  
         "inc(x,1);inc(x,1)*; x > 2"
         "x>2;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2";
      assert_equivalent "Greater than"  
         "x>2;x>1"
         "x>2"; 
      assert_equivalent "Commutativity-plus" 
         "x > 2 + y > 1"
         "y > 1 + x > 2";
      assert_equivalent "Idempotency-actions" 
         "inc(x,1) + inc(x,1)"
         "inc(x,1)";
      assert_equivalent "Test-in-loop1" 
         "(inc(x,1);x>1)*"
         "true + x>0;inc(x,1);inc(x,1)*"; 
      assert_not_equivalent "Test-in-loop2" 
         "(inc(x,1);x>1)*"
         "true + inc(x,1);inc(x,1)*"
    ]
end

module TestIncNat (T : TESTER) = struct
  module TI = T(IncNat)
  open TI

  let tests =
    [ assert_equivalent "Idempotency1" 
         "x > 2"  
         "x > 2";
      assert_equivalent "Idempotency2" 
         "inc(x)*; x > 2"  
         "inc(x)*; x > 2";
      assert_equivalent "Unrolling1" 
         "inc(x);inc(x)*; x > 2"
         "x>1;inc(x) + inc(x);inc(x);inc(x)*; x > 2";
      assert_equivalent "Unrolling2" 
         "inc(x)*; x > 2"  
         "x>2 + inc(x);inc(x)*; x > 2";
      assert_equivalent "Unrolling3" 
         "inc(x)*; x > 2"  
         "x>2 + inc(x)*; x > 2";
      assert_equivalent "Postcondition1" 
         "inc(x); inc(x); inc(x); x > 2"  
         "inc(x); inc(x); inc(x); x > 1"; 
      assert_not_equivalent "Postcondition2" 
         "inc(x); inc(x); inc(x); x > 2"  
         "inc(x); inc(x); inc(x); x > 3";
      assert_equivalent "Commutativity" 
         "inc(x);inc(y); x > 0; y > 0"
         "inc(x);inc(y); y > 0; x > 0";
      assert_not_equivalent "Initial Conditions" 
         "inc(x);inc(x)*; x > 2"
         "x>2;inc(x) + inc(x);inc(x);inc(x)*; x > 2";
      assert_equivalent "Greater than" 
         "x>2;x>1"
         "x>2";
      assert_equivalent "Commutativity-plus" 
         "x > 2 + y > 1"
         "y > 1 + x > 2";
      assert_equivalent "Idempotency-actions" 
         "inc(x) + inc(x)"
         "inc(x)";
      assert_equivalent "Test-in-loop1" 
         "(inc(x);x>1)*"
         "true + x>0;inc(x);inc(x)*"; 
      assert_not_equivalent "Test-in-loop2" 
         "(inc(x);x>1)*"
         "true + inc(x);inc(x)*";
      assert_equivalent "Canceled-set" 
         "set(x,0);x>0"
         "false";
      assert_equivalent "Set-canceled-pred" 
         "set(x,5);x>0"
         "set(x,5)";
      assert_not_equivalent "Tracing" 
         "(inc(x))*;set(x,0)"
         "set(x,0)"
    ]
end

module TestBoolean (T : TESTER) = struct
  module TB = T(Boolean)
  open TB

  let tests =
    [ assert_equivalent "Boolean-assign-eq"
         "set(x,T); x=T"
         "set(x,T)";
      assert_not_equivalent "Boolean-assign-neq"
         "set(x,T); x=F"
         "set(x,T)";
      assert_equivalent "Boolean-assign-eq2"
         "set(x,T); set(x,F); x=F"
         "set(x,T); set(x,F)";
     (* taking too long in normalization... *)     
(*      assert_equivalent  "Boolean-parity-loop"
         "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*"
         "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=F";
         assert_not_equivalent "Boolean-parity-loop2"
         "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*"
         "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=T"; *)
      assert_equivalent "Boolean-finiteness"
         "x=F + x=T"
         "true";
      assert_equivalent "Boolean-associativity"
         "(x=F + y=F) + z=F"
         "x=F + (y=F + z=F)";
      assert_equivalent "Boolean-multiple-vars"
         "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=T + x=F;y=F)"
         "(x=T; set(y,T) + x=F; set(y,F))";
      assert_not_equivalent "Boolean-multiple-vars2"
         "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=F + x=F;y=F)"
         "(x=T; set(y,T) + x=F; set(y,F))";
     (* taking too long in normalization... *)
     (* assert_equivalent "Boolean-unrolling"
         "set(x,T)*; x=T"
         "x=T + set(x,T); set(x,T)*; x=T"; *)
      assert_equivalent "Boolean-tree-ordering"
        "set(w,F); set(x,T); set(y,F); set(z,F); ((w=T + x=T + y=T + z=T); set(a,T) + (not (w=T + x=T + y=T + z=T)); set(a,F))"
        "set(w,F); set(x,T); set(y,F); set(z,F); (((w=T + x=T) + (y=T + z=T)); set(a,T) + (not ((w=T + x=T) + (y=T + z=T))); set(a,F))";
      assert_equivalent "KAT P* identity"
        "(a=T)*"
        "(a=T;a=T)* + a=T;(a=T;a=T)*"
    ]
end

module TestProduct (T : TESTER) = struct
  module TP = T(Product(Addition)(Boolean))
  open TP

  (* assert_equivalent 
      "y<1; (a=F + a=T; inc(y,1)); (b=F + b=T; inc(y,1)); (c=F + c=T; inc(y,1)); y>2"
      "a=T; b=T; c=T; inc(y,1); inc(y,1); inc(y,1)" *)

  let tests =
    [ assert_equivalent "Product-parsing"
        "set(x,T); x=T; inc(y,1)"
        "set(x,T); inc(y,1)";
      assert_not_equivalent "Product-action-ordering"
        "set(x,T); inc(y,1)"
        "inc(y,1); set(x,T)";
      assert_equivalent  "Product-population-count"
        "y<1; (a=F + a=T; inc(y,1)); y > 0"
        "y<1; a=T; inc(y,1)";
      assert_not_equivalent  "Product-population-count2"
        "y<1; (a=F + a=T; inc(y,1))"
        "a=T; inc(y,1)"
    ]
                                            
end
                                
module TestAdditionNormalization = TestAddition(NormalizationTester)
module TestAdditionAutomata = TestAddition(AutomataTester)

module TestIncNatNormalization = TestIncNat(NormalizationTester)
module TestIncNatAutomata = TestIncNat(AutomataTester)

module TestBooleanNormalization = TestBoolean(NormalizationTester)
module TestBooleanAutomata = TestBoolean(AutomataTester)

module TestProductNormalization = TestProduct(NormalizationTester)
module TestProductAutomata = TestProduct(AutomataTester)
                           
let main () =
  let open Alcotest in
  run "Equivalence" [
      "Addition normalization", TestAdditionNormalization.tests
    ; "IncNat normalization", TestIncNatNormalization.tests
    ; "Boolean normalization", TestBooleanNormalization.tests
    ; "Product normalization", TestProductNormalization.tests
    ; "Addition automata", TestAdditionAutomata.tests
    ; "IncNat automata", TestIncNatAutomata.tests
    ; "Boolean automata", TestBooleanAutomata.tests
    ; "Product automata", TestProductAutomata.tests
    ]
;;

main ()
