open Kat
open Addition
open Automata

module T = ANSITerminal
module K = Addition.K
module A = Automata(K)

exception Violation of string * string

type result = 
  | Success 
  | Failure of string * string

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

  let test0 () = 
    assert_equivalent 
      "x > 2"  
      "x > 2"

  let test1 () = 
    assert_equivalent 
      "inc(x,1)*; x > 2"  
      "inc(x,1)*; x > 2"

  let test2 () = 
    assert_equivalent 
      "inc(x,1);inc(x,1)*; x > 2"
      "x>1;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2"

  let test3 () = 
    assert_equivalent 
      "inc(x,1)*; x > 2"  
      "x>2 + inc(x,1);inc(x,1)*; x > 2"

  let test4 () = 
    assert_equivalent 
      "inc(x,1); inc(x,1); inc(x,1); x > 2"  
      "inc(x,1); inc(x,1); inc(x,1); x > 1"

  let test5 () = 
    assert_not_equivalent 
      "inc(x,1); inc(x,1); inc(x,1); x > 2"  
      "inc(x,1); inc(x,1); inc(x,1); x > 3"
   
  let test6 () = 
    assert_equivalent 
      "inc(x,1);inc(y,1); x > 0; y > 0"
      "inc(x,1);inc(y,1); y > 0; x > 0"

  let test7 () = 
    assert_not_equivalent 
      "inc(x,1);inc(x,1)*; x > 2"
      "x>2;inc(x,1) + inc(x,1);inc(x,1);inc(x,1)*; x > 2"

  let test8 () = 
    assert_equivalent 
      "x>2;x>1"
      "x>2"

  let test9 () = 
    assert_equivalent
      "x > 2 + y > 1"
      "y > 1 + x > 2"

  let test10 () = 
    assert_equivalent
      "inc(x,1) + inc(x,1)"
      "inc(x,1)"

  let test11 () = 
    assert_equivalent
      "(inc(x,1);x>1)*"
      "true + x>0;inc(x,1);inc(x,1)*"

  let test12 () = 
    assert_not_equivalent
      "(inc(x,1);x>1)*"
      "true + inc(x,1);inc(x,1)*"

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
     "Test-in-loop2" >:: test12]

end;;

check Unit.tests