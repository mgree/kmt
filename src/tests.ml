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
    [ assert_equivalent "predicate reflexivity"  
         "x > 2"  
         "x > 2";
      assert_equivalent "star reflexivity"  
         "inc(x,1)*; x > 2"  
         "inc(x,1)*; x > 2";
      assert_equivalent "unrolling 1"  
         "inc(x,1);inc(x,1)*; x > 2"
         "x>1;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2";
      assert_equivalent "unrolling 2"  
         "inc(x,1)*; x > 2"  
         "x>2 + inc(x,1);inc(x,1)*; x > 2";
      assert_equivalent "unrolling 3"  
         "inc(x,1)*; x > 2"  
         "x>2 + inc(x,1)*; x > 2";
      assert_equivalent "postcondition 1"  
         "inc(x,1); inc(x,1); inc(x,1); x > 2"  
         "inc(x,1); inc(x,1); inc(x,1); x > 1"; 
      assert_not_equivalent "postcondition 2"  
         "inc(x,1); inc(x,1); inc(x,1); x > 2"  
         "inc(x,1); inc(x,1); inc(x,1); x > 3";
      assert_equivalent "commutativity"  
         "inc(x,1);inc(y,1); x > 0; y > 0"
         "inc(x,1);inc(y,1); y > 0; x > 0";
      assert_not_equivalent "initial conditions"  
         "inc(x,1);inc(x,1)*; x > 2"
         "x>2;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2";
      assert_equivalent "Greater than"  
         "x>2;x>1"
         "x>2"; 
      assert_equivalent "commutativity plus" 
         "x > 2 + y > 1"
         "y > 1 + x > 2";
      assert_equivalent "idempotency actions" 
         "inc(x,1) + inc(x,1)"
         "inc(x,1)";
      assert_equivalent "test in loop 1" 
         "(inc(x,1);x>1)*"
         "true + x>0;inc(x,1);inc(x,1)*"; 
      assert_not_equivalent "test in loop 2" 
         "(inc(x,1);x>1)*"
         "true + inc(x,1);inc(x,1)*"
    ]
end

module TestIncNat (T : TESTER) = struct
  module TI = T(IncNat)
  open TI

  let tests =
    [ assert_equivalent "idempotency 1" 
         "x > 2"  
         "x > 2";
      assert_equivalent "idempotency 2" 
         "inc(x)*; x > 2"  
         "inc(x)*; x > 2";
      assert_equivalent "unrolling 1" 
         "inc(x);inc(x)*; x > 2"
         "x>1;inc(x) + inc(x);inc(x);inc(x)*; x > 2";
      assert_equivalent "unrolling 2" 
         "inc(x)*; x > 2"  
         "x>2 + inc(x);inc(x)*; x > 2";
      assert_equivalent "unrolling 3" 
         "inc(x)*; x > 2"  
         "x>2 + inc(x)*; x > 2";
      assert_equivalent "postcondition 1" 
         "inc(x); inc(x); inc(x); x > 2"  
         "inc(x); inc(x); inc(x); x > 1"; 
      assert_not_equivalent "postcondition 2" 
         "inc(x); inc(x); inc(x); x > 2"  
         "inc(x); inc(x); inc(x); x > 3";
      assert_equivalent "commutativity" 
         "inc(x);inc(y); x > 0; y > 0"
         "inc(x);inc(y); y > 0; x > 0";
      assert_not_equivalent "initial Conditions" 
         "inc(x);inc(x)*; x > 2"
         "x>2;inc(x) + inc(x);inc(x);inc(x)*; x > 2";
      assert_equivalent "greater than" 
         "x>2;x>1"
         "x>2";
      assert_equivalent "commutativity plus" 
         "x > 2 + y > 1"
         "y > 1 + x > 2";
      assert_equivalent "idempotency actions" 
         "inc(x) + inc(x)"
         "inc(x)";
      assert_equivalent "test in loop 1" 
         "(inc(x);x>1)*"
         "true + x>0;inc(x);inc(x)*"; 
      assert_not_equivalent "test in loop 2" 
         "(inc(x);x>1)*"
         "true + inc(x);inc(x)*";
      assert_equivalent "canceled set" 
         "set(x,0);x>0"
         "false";
      assert_equivalent "set canceled pred" 
         "set(x,5);x>0"
         "set(x,5)";
      assert_not_equivalent "tracing" 
         "(inc(x))*;set(x,0)"
         "set(x,0)"
    ]
end

module TestBoolean (T : TESTER) = struct
  module TB = T(Boolean)
  open TB

  let tests =
    [ assert_equivalent "boolean assign eq"
         "set(x,T); x=T"
         "set(x,T)";
      assert_not_equivalent "boolean assign neq"
         "set(x,T); x=F"
         "set(x,T)";
      assert_equivalent "boolean assign eq 2"
         "set(x,T); set(x,F); x=F"
         "set(x,T); set(x,F)";
      assert_equivalent  "boolean parity loop"
        "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*"
        "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=F";
      assert_not_equivalent "boolean parity loop 2"
        "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*"
        "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=T";
      assert_equivalent "boolean finiteness"
         "x=F + x=T"
         "true";
      assert_equivalent "boolean associativity"
         "(x=F + y=F) + z=F"
         "x=F + (y=F + z=F)";
      assert_equivalent "boolean multiple vars"
         "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=T + x=F;y=F)"
         "(x=T; set(y,T) + x=F; set(y,F))";
      assert_not_equivalent "boolean multiple vars 2"
         "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=F + x=F;y=F)"
         "(x=T; set(y,T) + x=F; set(y,F))";
      assert_equivalent "boolean unrolling"
         "set(x,T)*; x=T"
         "x=T + set(x,T); set(x,T)*; x=T";
      assert_equivalent "boolean tree ordering"
        "set(w,F); set(x,T); set(y,F); set(z,F); ((w=T + x=T + y=T + z=T); set(a,T) + (not (w=T + x=T + y=T + z=T)); set(a,F))"
        "set(w,F); set(x,T); set(y,F); set(z,F); (((w=T + x=T) + (y=T + z=T)); set(a,T) + (not ((w=T + x=T) + (y=T + z=T))); set(a,F))";
      assert_equivalent "kat p* identity"
        "(a=T)*"
        "(a=T;a=T)* + a=T;(a=T;a=T)*"
    ]
end

module TestProduct (T : TESTER) = struct
  module TP = T(Product(Addition)(Boolean))
  open TP

  (* assert_equivalent "is this even right?"
      "y<1; (a=F + a=T; inc(y,1)); (b=F + b=T; inc(y,1)); (c=F + c=T; inc(y,1)); y>2"
      "a=T; b=T; c=T; inc(y,1); inc(y,1); inc(y,1)" *)

  let tests =
    [ assert_equivalent "product parsing"
        "set(x,T); x=T; inc(y,1)"
        "set(x,T); inc(y,1)";
      assert_not_equivalent "product action ordering"
        "set(x,T); inc(y,1)"
        "inc(y,1); set(x,T)";
      assert_equivalent  "product population count"
        "y<1; (a=F + a=T; inc(y,1)); y > 0"
        "y<1; a=T; inc(y,1)";
      assert_not_equivalent  "product population count 2"
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
  run ~show_errors:true "equivalence" [
      "addition normalization", TestAdditionNormalization.tests
    ; "incnat normalization", TestIncNatNormalization.tests
    ; "boolean normalization", TestBooleanNormalization.tests
    ; "product normalization", TestProductNormalization.tests
    ; "addition automata", TestAdditionAutomata.tests
    ; "incnat automata", TestIncNatAutomata.tests
    ; "boolean automata", TestBooleanAutomata.tests
    ; "product automata", TestProductAutomata.tests
    ]
;;

main ()
