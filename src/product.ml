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

    let rec to_test_left (a : K.Test.t) (f : T2.K.A.t -> T1.K.Test.t) : T1.K.Test.t = 
      match a.node with 
      | Zero -> T1.K.zero ()
      | One -> T1.K.one ()
      | Theory (Left x) -> T1.K.theory x
      | Theory (Right y) -> f y 
      | Not x -> T1.K.not (to_test_left x f)
      | PPar(x,y) -> T1.K.ppar (to_test_left x f) (to_test_left y f)
      | PSeq(x,y) -> T1.K.pseq (to_test_left x f) (to_test_left y f)
      | Placeholder i -> T1.K.placeholder i
  
    let rec to_test_right (a : K.Test.t) (f : T1.K.A.t -> T2.K.Test.t) : T2.K.Test.t = 
      match a.node with 
      | Zero -> T2.K.zero ()
      | One -> T2.K.one ()
      | Theory (Right x) -> T2.K.theory x
      | Theory (Left y) -> f y 
      | Not x -> T2.K.not (to_test_right x f)
      | PPar(x,y) -> T2.K.ppar (to_test_right x f) (to_test_right y f)
      | PSeq(x,y) -> T2.K.pseq (to_test_right x f) (to_test_right y f)
      | Placeholder i -> T2.K.placeholder i
  
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

    let merge (p1 : P.t) (p2 : P.t) : P.t = failwith "product merge undefined"

    (* TODO MMG 2020-02-28 we could have a real definition here... *)
    let reduce a p = failwith "product reduce undefined"

    let variable p = 
      match p with 
      | Left x -> T1.variable x 
      | Right y -> T2.variable y

    let variable_test a = 
      match a with 
      | Left x -> T1.variable_test x 
      | Right y -> T2.variable_test y

    let unbounded () = T1.unbounded() || T2.unbounded()
  
    let rec only_left (a : K.Test.t) : bool = 
      match a.node with 
      | Zero | One | Theory (Left _) -> true
      | Theory (Right _) -> false 
      | Not x -> only_left x
      | PPar(x,y) | PSeq(x,y) -> (only_left x && only_left y)
      | Placeholder i -> failwith "impossible"

    let rec only_right (a : K.Test.t) : bool = 
      match a.node with  
      | Zero | One | Theory (Right _) -> true
      | Theory (Left _) -> false 
      | Not x -> only_right x
      | PPar(x,y) | PSeq(x,y) -> (only_right x && only_right y)
      | Placeholder i -> failwith "impossible"

    let theory_to_z3_expr (a : A.t) (ctx : Z3.context) (map : Z3.Expr.expr StrMap.t) = 
      match a with 
      | Left x -> T1.theory_to_z3_expr x ctx map 
      | Right y -> T2.theory_to_z3_expr y ctx map
  
    let create_z3_var (str,a) (ctx : Z3.context) (solver : Z3.Solver.solver) : Z3.Expr.expr = 
      match a with 
      | Left x -> T1.create_z3_var (str,x) ctx solver 
      | Right y -> T2.create_z3_var (str,y) ctx solver

    let satisfiable (a: K.Test.t) = 
      if only_left a then T1.satisfiable (to_test_left a (fun _ -> failwith "product sat left error"))
      else if only_right a then T2.satisfiable (to_test_right a (fun _ -> failwith "product sat right error"))
      else K.z3_satisfiable a
      
  end  

  include Implementation
end
