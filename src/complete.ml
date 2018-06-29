open Kat
open Common
open BatSet
open SafeMap
open Hashcons

(* Given a theory, create a 'complete' theory that maps variables to actions *)

module CompleteTheoryAux
    (T : THEORY)
    (M : SafeMap.S with type key = string and type value = T.P.t) :
  THEORY with type A.t = T.A.t and type P.t = M.t = struct
  
  module rec Implementation : THEORY with type A.t = T.A.t and type P.t = M.t = struct
    module K = KAT (Implementation)
    module Test = K.Test
    module Term = K.Term
    module A = T.A
    module P = M

    let from_p (p: T.P.t) : P.t = M.singleton (T.variable p) p

    (* we use this to ensure all terms are hashconsed *)
    let rec from_test (x: T.Test.t) : Test.t =
      match x.node with
      | Zero -> K.zero ()
      | One -> K.one ()
      | Theory a -> K.theory a
      | Not b -> K.not (from_test b)
      | PPar (b, c) -> K.ppar (from_test b) (from_test c)
      | PSeq (b, c) -> K.pseq (from_test b) (from_test c)
      | Placeholder _ -> failwith "impossible"


    let rec from (x: T.Term.t) : Term.t =
      match x.node with
      | Action (i, p) -> K.action (from_p p)
      | Pred a -> K.pred (from_test a)
      | Par (a, b) -> K.par (from a) (from b)
      | Seq (a, b) -> K.seq (from a) (from b)
      | Star a -> K.star (from a)


    let satisfiable x = failwith ""

    let theory_to_z3_expr a ctx map = failwith ""
  
    let create_z3_var str ctx solver = failwith ""

    let variable x = ""

    let variable_test x = ""

    let unbounded () = T.unbounded ()

    let simplify_or x y = T.simplify_or x y

    let simplify_and x y = T.simplify_and x y

    let simplify_not x = T.simplify_not x

    let subterms x = failwith ""

    let parse x es =
      match T.parse x es with Left a -> Left a | Right p -> Right (from_p p)


    let merge (x: P.t) (y: P.t) : P.t =
      let aux k xo yo =
        match (xo, yo) with
        | None, None -> None
        | Some p, Some q -> Some (T.merge p q)
        | Some _, _ -> xo
        | _, Some _ -> yo
      in
      P.merge aux x y


    let reduce a p = None

    let push_back (p: P.t) (a: A.t) : K.Test.t PSet.t =
      let aux (k: string) (v: T.P.t) (acc: K.Test.t PSet.t) =
        PSet.fold
          (fun test acc2 ->
            let set =
              match test.node with
              | Theory a -> T.push_back v a
              | _ -> K.push_back_test (M.singleton k v) test
            in
            PSet.union acc2 set )
          acc
          (PSet.create T.Test.compare)
      in
      (* map back using the K module constructors to ensure hash consing *)
      let ret =
        P.fold aux p (PSet.singleton ~cmp:T.Test.compare (K.theory a))
      in
      PSet.map from_test ret
  end

  include Implementation
end

module CompleteTheory (T : THEORY) = struct
  module M = SafeMap.Make (StrType) (T.P)
  include CompleteTheoryAux (T) (M)
end
