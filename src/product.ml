open Kat 
open Syntax
open Common
open Hashcons
open Range

module Product(T1 : THEORY) (T2: THEORY) : (THEORY with type A.t = (T1.A.t, T2.A.t) either and type P.t = (T1.P.t, T2.P.t) either ) = struct 

  module rec Implementation : (THEORY with type A.t = (T1.A.t, T2.A.t) either and type P.t = (T1.P.t, T2.P.t) either ) = struct

    module K = KAT(Implementation)
    module Test = K.Test
    module Term = K.Term
    module P = Common.Either.Make(T1.P)(T2.P)
    module A = Common.Either.Make(T1.A)(T2.A)

    let parse name es : (A.t, P.t) either =
      try 
        match T1.parse name es with 
        | Left x -> Left (Left x)
        | Right y -> Right (Left y) 
      with _ -> begin 
        try 
          match T2.parse name es with 
          | Left x -> Left (Right x)
          | Right y -> Right (Right y) 
        with _ -> 
          failwith ("Cannot create theory object from (" ^ name ^ ") and parameters")
      end

    open BatSet

    let rec from_test_left (a : T1.K.Test.t) : K.Test.t = 
      match a.node with 
      | Zero -> K.zero ()
      | One -> K.one ()
      | Theory x -> K.theory (Left x) 
      | Not x -> K.not (from_test_left x)
      | PPar(x,y) -> K.ppar (from_test_left x) (from_test_left y)
      | PSeq(x,y) -> K.pseq (from_test_left x) (from_test_left y)
      | Placeholder i -> K.placeholder i

    let rec from_test_right (a : T2.K.Test.t) : K.Test.t = 
      match a.node with 
      | Zero -> K.zero ()
      | One -> K.one ()
      | Theory x -> K.theory (Right x) 
      | Not x -> K.not (from_test_right x)
      | PPar(x,y) -> K.ppar (from_test_right x) (from_test_right y)
      | PSeq(x,y) -> K.pseq (from_test_right x) (from_test_right y)
      | Placeholder i -> K.placeholder i

    let convert_from_left set = 
      BatSet.PSet.fold 
        (fun v acc -> BatSet.PSet.add (from_test_left v) acc) 
        set 
        (BatSet.PSet.create K.Test.compare)

    let convert_from_right set = 
      BatSet.PSet.fold 
        (fun v acc -> BatSet.PSet.add (from_test_right v) acc) 
        set 
        (BatSet.PSet.create K.Test.compare)

    let rec subterms (a : K.A.t) = 
      match a with 
      | Left x -> convert_from_left (T1.subterms x)
      | Right y -> convert_from_right (T2.subterms y)

    let rec push_back p a =
      match p,a with 
      | Left p, Left a -> convert_from_left (T1.push_back p a)
      | Right p, Right a -> convert_from_right (T2.push_back p a)
      | Left _, Right _
      | Right _, Left _ -> PSet.singleton ~cmp:K.Test.compare (K.theory a)

    let simplify_or a b =
      match a,b with 
      | Left x, Left y -> begin
          match T1.simplify_or x y with 
          | None -> None 
          | Some z -> Some (from_test_left z)
        end
      | Right x, Right y -> begin
        match T2.simplify_or x y with 
        | None -> None 
        | Some z -> Some (from_test_right z)
      end
      | _, _ -> None 

    let simplify_and a b =
      match a,b with 
      | Left x, Left y -> begin
          match T1.simplify_and x y with 
          | None -> None 
          | Some z -> Some (from_test_left z)
        end
      | Right x, Right y -> begin
        match T2.simplify_and x y with 
        | None -> None 
        | Some z -> Some (from_test_right z)
      end
      | _, _ -> None 

    let simplify_not a = 
      match a with 
      | Left x -> begin
        match T1.simplify_not x with 
        | None -> None 
        | Some z -> Some (from_test_left z)
        end
      | Right y -> begin
        match T2.simplify_not y with 
        | None -> None 
        | Some z -> Some (from_test_right z)
        end

    let satisfiable (a : Test.t) : bool = failwith ""
      (* match a with 
      | Left x -> T1.satisfiable x
      | Right y -> T2.satisfiable y *)

    let merge (p1 : P.t) (p2 : P.t) : P.t = failwith ""

    let reduce a p = failwith ""

    let variable _ = failwith ""

    let unbounded () = T1.unbounded() || T2.unbounded()
    
  end  

  include Implementation
end