open Kat
open Syntax
open Common
open Hashcons
open Range

type a = Gt of string * int [@@deriving eq]

type p = Increment of string | Assign of string * int [@@deriving eq]

let compare_a (Gt (x,n)) (Gt (y,m)) =
  let cmp = StrType.compare x y in
  if cmp <> 0 then cmp
  else n - m

let compare_p p q =
  match (p, q) with
  | Increment x, Increment y -> StrType.compare x y
  | Assign (x,i), Assign (y,j) ->
     let cmp = StrType.compare x y in
     if cmp <> 0 then cmp
     else i - j
  | Increment _, Assign _ -> -1    
  | Assign _, Increment _ -> 1


module rec IncNat : THEORY with type A.t = a and type P.t = p = struct
  module K = KAT (IncNat)
  module Test = K.Test
  module Term = K.Term

  module P : CollectionType with type t = p = struct
    type t = p
    let compare = compare_p
    let hash = Hashtbl.hash
    let equal = equal_p
    let show = function
      | Increment x -> "inc (" ^ x ^ ")"
      | Assign (x,i) -> "set (" ^ x ^ "," ^ string_of_int i ^ ")"
  end

  module A : CollectionType with type t = a = struct
    type t = a
    let compare = compare_a
    let hash = Hashtbl.hash
    let equal = equal_a
    let show = function
      | Gt (x, n) -> x ^ ">" ^ string_of_int n
  end

  let variable =  function
    | Increment x -> x
    | Assign (x,_) -> x

  let variable_test (Gt (x,_)) = x

  let parse name es =
    match (name, es) with
    | "inc", [(EId s1)] -> Right (Increment s1)
    | "set", [(EId s1);EId s2] -> Right (Assign (s1, int_of_string s2))
    | ">", [(EId s1); (EId s2)] -> Left (Gt (s1, int_of_string s2))
    | _, _ ->
        failwith ("Cannot create theory object from (" ^ name ^ ") and parameters")

  open BatSet

  let push_back p a =
    match (p,a) with
    | (Increment x, Gt (_, j)) when 1 > j -> PSet.singleton ~cmp:K.Test.compare (K.one ())
    | (Increment x, Gt (y, j)) when x = y ->
       PSet.singleton ~cmp:K.Test.compare (K.theory (Gt (y, j - 1)))
    | (Assign (x,i), Gt (y,j)) when x = y -> PSet.singleton ~cmp:K.Test.compare (if i > j then K.one () else K.zero ())
    | _ -> PSet.singleton ~cmp:K.Test.compare (K.theory a)


  let rec subterms x =
    match x with
    | Gt (_, 0) -> PSet.singleton ~cmp:K.Test.compare (K.theory x)
    | Gt (v, i) -> PSet.add (K.theory x) (subterms (Gt (v, i - 1)))


  let simplify_and a b =
    match (a, b) with
    | Gt (x, v1), Gt (y, v2) when x = y -> Some (K.theory (Gt (x, max v1 v2)))
    | _, _ -> None


  let simplify_not a = None

  let simplify_or a b = None

  let merge (p1: P.t) (p2: P.t) : P.t = p2

  let reduce a p = Some p

  let unbounded () = true

  open Z3

  let create_z3_var (str,a) (ctx : Z3.context) (solver : Z3.Solver.solver) : Z3.Expr.expr = 
    let sym = Symbol.mk_string ctx str in
    let int_sort = Arithmetic.Integer.mk_sort ctx in
    let xc = Expr.mk_const ctx sym int_sort in
    let is_nat =
      Arithmetic.mk_ge ctx xc (Arithmetic.Integer.mk_numeral_i ctx 0)
    in
    Solver.add solver [is_nat];
    xc

  let theory_to_z3_expr (a : A.t) (ctx : Z3.context) (map : Z3.Expr.expr StrMap.t) : Z3.Expr.expr = 
    match a with
    | Gt (x, v) ->
        let var = StrMap.find x map in
        let value = Arithmetic.Integer.mk_numeral_i ctx v in
        Arithmetic.mk_gt ctx var value

  module H = Hashtbl.Make (K.Test)

  let tbl = H.create 2048

  let rec can_use_fast_solver (a: K.Test.t) =
    match a.node with
    | One | Zero | Placeholder _ | Theory _ -> true
    | PPar _ -> false
    | PSeq (b, c) -> can_use_fast_solver b && can_use_fast_solver c
    | Not {node= Theory _} -> true
    | Not _ -> false

  let satisfiable (a: K.Test.t) =
    try H.find tbl a with _ ->
      (* Printf.printf "Checking Sat %s\n" (K.Test.show a); *)
      debug (fun () -> Printf.printf "SAT: %s" (K.Test.show a)) ;
      if not (can_use_fast_solver a) then (
        debug (fun () -> Printf.printf " SLOW\n") ;
        let ret = K.z3_satisfiable a in
        H.add tbl a ret ; ret )
      else (
        debug (fun () -> Printf.printf " FAST\n") ;
        let mergeOp map1 map2 op =
          StrMap.merge
            (fun _ v1 v2 ->
              match (v1, v2) with
              | None, _ -> v2
              | _, None -> v1
              | Some x, Some y -> Some (op x y) )
            map1 map2
        in
        let rec aux (a: K.Test.t) : Range.t StrMap.t =
          match a.node with
          | One | Zero | Placeholder _ -> failwith "IncNat: satisfiability"
          | Not b -> StrMap.map Range.negate (aux b)
          | PPar (b, c) -> mergeOp (aux b) (aux c) Range.union
          | PSeq (b, c) -> mergeOp (aux b) (aux c) Range.inter
          | Theory Gt (x, v) ->
              StrMap.singleton x (Range.from_range (v + 1, max_int))
        in
        match a.node with
        | One -> true
        | Zero -> false
        | _ ->
            let result = aux a in
            let ret =
              StrMap.for_all (fun _ r -> not (Range.is_false r)) result
            in
            (* Printf.printf "Actual Result: %b\n" ret; *)
            H.add tbl a ret ; ret )
end
