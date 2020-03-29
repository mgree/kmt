open Common
open Kat
open Incnat
open Addition
open Boolean
open Product
open Automata
open Decide

type mode = Normalization | Automata

module type TESTER =
  functor (T : THEORY) ->
  sig
    type t = string

    val mode : mode
           
    val pp : t Fmt.t

    val equal : t -> t -> bool
    
    val assert_equivalent : ?speed:Alcotest.speed_level ->
                            string -> string -> string -> unit Alcotest.test_case
    val assert_not_equivalent : ?speed:Alcotest.speed_level ->
                                string -> string -> string -> unit Alcotest.test_case
  end

module AutomataTester(T : THEORY) = struct
  module K = T.K
  module A = Automata(K)

  type t = string

  let mode = Automata
         
  let pp = Fmt.string
         
  let equal s1 s2 =          
    let x = K.parse s1 in 
    let y = K.parse s2 in 
    let a1 = A.of_term x in 
    let a2 = A.of_term y in 
    A.equivalent a1 a2

  let equivalent : string Alcotest.testable = Alcotest.testable pp equal

  let assert_equivalent ?speed:(speed=`Quick) name l r =
    Alcotest.test_case name speed (fun () -> Alcotest.(check equivalent) "equivalent" l r)
  let assert_not_equivalent ?speed:(speed=`Quick) name l r =
    Alcotest.test_case name speed (fun () -> Alcotest.(check (Alcotest.neg equivalent)) "inequivalent" l r)
end

module NormalizationTester(T : THEORY) = struct
  module K = T.K
  module D = Decide(T)

  type t = string

  let mode = Normalization

  let pp = Fmt.string

  let equal s1 s2 =         
    let p = K.parse s1 in 
    let q = K.parse s2 in 
    D.equivalent p q
    
  let equivalent : string Alcotest.testable = Alcotest.testable pp equal

  let assert_equivalent ?speed:(speed=`Quick) name l r =
    Alcotest.test_case name speed (fun () -> Alcotest.(check equivalent) "equivalent" l r)
  let assert_not_equivalent ?speed:(speed=`Quick) name l r =
    Alcotest.test_case name speed (fun () -> Alcotest.(check (Alcotest.neg equivalent)) "inequivalent" l r)
end

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
    [ assert_equivalent "assign eq"
         "set(x,T); x=T"
         "set(x,T)";
      assert_not_equivalent "assign neq"
         "set(x,T); x=F"
         "set(x,T)";
      assert_equivalent "assign eq 2"
         "set(x,T); set(x,F); x=F"
         "set(x,T); set(x,F)";
      assert_equivalent  "parity loop"
        "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*"
        "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=F";
      assert_not_equivalent "parity loop 2"
        "x=F; ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*"
        "     ( (x=T; set(x,F) + x=F; set(x,T));(x=T; set(x,F) + x=F; set(x,T)) )*; x=T";
      assert_equivalent "finiteness"
         "x=F + x=T"
         "true";
      assert_equivalent "associativity"
         "(x=F + y=F) + z=F"
         "x=F + (y=F + z=F)";
      assert_equivalent "multiple vars"
         "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=T + x=F;y=F)"
         "(x=T; set(y,T) + x=F; set(y,F))";
      assert_not_equivalent "multiple vars 2"
         "(x=T; set(y,T) + x=F; set(y,F)); (x=T;y=F + x=F;y=F)"
         "(x=T; set(y,T) + x=F; set(y,F))";
      assert_equivalent "unrolling"
         "set(x,T)*; x=T"
         "x=T + set(x,T); set(x,T)*; x=T";
      assert_equivalent "kat p* identity"
        "(a=T)*"
        "(a=T;a=T)* + a=T;(a=T;a=T)*";
      assert_equivalent "toggle star"
        "(set(x,T) + set(y,T) + set(x,F) + set(y,T))*"
        "(set(x,F) + set(y,T) + set(x,T) + set(y,T))*"
    ] @ (if mode = Automata
         then []
         else [ assert_equivalent "tree ordering"
                  "set(w,F); set(x,T); set(y,F); set(z,F); ((w=T + x=T + y=T + z=T); set(a,T) + (not (w=T + x=T + y=T + z=T)); set(a,F))"
                  "set(w,F); set(x,T); set(y,F); set(z,F); (((w=T + x=T) + (y=T + z=T)); set(a,T) + (not ((w=T + x=T) + (y=T + z=T))); set(a,F))"
           ])

  let denesting_tests =
    ["x=F;set(x,T)"; "y=F;set(y,T)"; "x=T;set(x,F)"; "y=T;set(y,F)"]
    |> permutations
    |> List.map (List.fold_left (fun acc e -> e ^ add_sep " + " acc) "")
    |> List.map (fun inner -> "(" ^ inner ^ ")*")
    |> unique_pairs
    |> List.map (fun (lhs, rhs) -> assert_equivalent (lhs ^ " = " ^ rhs) lhs rhs)
end
                                
module TestProduct (T : TESTER) = struct
  module TP = T(Product(Addition)(Boolean))
  open TP

  let slow = if mode = Automata then `Slow else `Quick
     
  let tests =
    [ assert_equivalent "actions parse"
        "set(x,T); x=T; inc(y,1)"
        "set(x,T); inc(y,1)";
      assert_not_equivalent "actions commute"
        "set(x,T); inc(y,1)"
        "inc(y,1); set(x,T)";
      assert_equivalent  "population count"
        "y<1; (a=F + a=T; inc(y,1)); y > 0"
        "y<1; a=T; inc(y,1)";
      assert_not_equivalent ~speed:slow "population count 2"
        "y<1; (a=F + a=T; inc(y,1))"
        "a=T; inc(y,1)";
      assert_equivalent ~speed:slow "population count 3"
        "y<1; (true + a=T; inc(y,1)); (true + b=T; inc(y,1)); (true + c=T; inc(y,1)); y>2"      
        "y<1; a=T; b=T; c=T; inc(y,1); inc(y,1); inc(y,1)";
      assert_equivalent ~speed:slow "population count 3 (variant)"
        "y<1; (a=F + a=T; inc(y,1)); (b=F + b=T; inc(y,1)); (c=F + c=T; inc(y,1)); y>2"
        "y<1; a=T; b=T; c=T; inc(y,1); inc(y,1); inc(y,1)";
(*      assert_not_equivalent "population count: mismatched domain (regression)"
       "y<1; (a=F + a=T; inc(y,1)); not (y < 1)" "a=T;inc(y,1)" *)
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
  Alcotest.run "equivalence" [
      "addition normalization", TestAdditionNormalization.tests
    ; "incnat normalization", TestIncNatNormalization.tests
    ; "boolean normalization", TestBooleanNormalization.tests
    ; "product normalization", TestProductNormalization.tests
    ; "addition automata", TestAdditionAutomata.tests
    ; "incnat automata", TestIncNatAutomata.tests
    ; "boolean automata", TestBooleanAutomata.tests
    ; "product automata", TestProductAutomata.tests
    ; "denesting normalization",
      TestBooleanNormalization.denesting_tests
    ; "denesting automata",
      TestBooleanAutomata.denesting_tests
    ]
;;

main ()
