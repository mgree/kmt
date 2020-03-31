open Kat
open Common
open Hashcons

type 'a ltlf =
  | Base of 'a
  | Last of 'a ltlf pred
  | Since of 'a ltlf pred * 'a ltlf pred

module LTLF (T : THEORY) :
  THEORY with type A.t = T.A.t ltlf and type P.t = T.P.t =
struct
  module rec Implementation :
    THEORY with type A.t = T.A.t ltlf and type P.t = T.P.t =
  struct
    module K = KAT(Implementation)
    module Test = K.Test
    module Term = K.Term
    module P = T.P

    let name () = "ltlf(" ^ T.name () ^ ")"
             
    let hash_ltlf x =
      match x with
      | Base a -> T.A.hash a
      | Last a -> 3 * K.Test.hash a + 11
      | Since (a, b) -> 7 * K.Test.hash a + 11 * K.Test.hash b + 17

    let unbounded () = T.unbounded ()

    let variable _p =
      failwith "variable undefined for ltlf"
                 
    let variable_test _a =
      failwith "variable_test undefined for ltlf"

    let reduce _a _p = None

    let merge _p1 p2 = p2
      
    let theory_to_z3_expr _a (_ctx : Z3.context) (_map : Z3.Expr.expr StrMap.t) =
      failwith "theory_to_z3_expr undefined for ltlf"

    let create_z3_var (_str,_a) (_ctx : Z3.context) (_solver : Z3.Solver.solver)  : Z3.Expr.expr =
      failwith "create_z3_var undefined for ltlf"
      
    let base x = Base x

    let last x = Last x

    let since x y = Since (x, y)

    module A : CollectionType with type t = T.A.t ltlf = struct
      type t = T.A.t ltlf

      let hash = hash_ltlf

      let compare = Stdlib.Pervasives.compare

      let equal x y = Stdlib.Pervasives.compare x y = 0

      let show x =
        match x with
        | Base a -> T.A.show a
        | Last a -> "last(" ^ K.Test.show a ^ ")"
        | Since (a, b) -> "since(" ^ K.Test.show a ^ "," ^ K.Test.show b ^ ")"
    end

    let parse name es : (A.t, P.t) either =
      match (name, es) with
      | "last", [e1] -> Left (last (K.test_of_expr e1))
      | "since", [e1; e2] ->
          Left (since (K.test_of_expr e1) (K.test_of_expr e2))
      | _, _ ->
        match T.parse name es with
        | Right v -> Right v
        | Left v -> Left (base v)

    open BatSet

    let rec from_test (a: T.K.Test.t) : K.Test.t =
      match a.node with
      | Zero -> K.zero ()
      | One -> K.one ()
      | Theory x -> K.theory (base x)
      | Not x -> K.not (from_test x)
      | PPar (x, y) -> K.ppar (from_test x) (from_test y)
      | PSeq (x, y) -> K.pseq (from_test x) (from_test y)
      | Placeholder i -> K.placeholder i

    let subterms (a: K.A.t) =
      match a with
      | Base x -> PSet.map from_test (T.subterms x)
      | Last x -> PSet.add (K.theory a) (K.subterms x)
      | Since (x, y) ->
          PSet.union (K.subterms x) (K.subterms y) |> PSet.add (K.theory a)


    let push_back p t =
      match t with
      | Base x ->
          let pbs = T.push_back p x in
          let b = PSet.create K.Test.compare in
          PSet.fold (fun a acc -> PSet.add (from_test a) acc) pbs b
      | Last a -> PSet.singleton ~cmp:K.Test.compare a
      | Since (a, b) ->
          let x1 = K.push_back_test p b in
          let x2 = K.push_back_test p a in
          let x2 = PSet.map (fun a -> K.pseq a (K.theory t)) x2 in
          PSet.union x1 x2

    let simplify_or _a _b = None

    let simplify_and _a _b = None

    let simplify_not _a = None

    let satisfiable (_a: Test.t) : bool = failwith "not implemented"
  end

  include Implementation
end
