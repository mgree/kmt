open Kat
open Syntax
open Common
open Hashcons
open Range

type a = Bool of string * bool [@@deriving eq]

type p = Assign of string * bool [@@deriving eq]

let get_name_a = function Bool (x, _) -> x

let get_name_p (Assign (x, _)) = x

let get_value = function Bool (_, v) -> v

let get_value_int = function Bool (_, v) -> if v then 1 else 0

let compare_a a b =
  let cmp = StrType.compare (get_name_a a) (get_name_a b) in
  if cmp <> 0 then cmp else get_value_int a - get_value_int b


let compare_p p q =
  match (p, q) with Assign (x, i), Assign (y, j) ->
    let cmp = StrType.compare x y in
    if cmp <> 0 then cmp else (if i then 1 else 0) - if j then 1 else 0


module rec Boolean : THEORY with type A.t = a and type P.t = p = struct
  module K = KAT (Boolean)
  module Test = K.Test
  module Term = K.Term

  module P : CollectionType with type t = p = struct
    type t = p
    let compare = compare
    let hash = Hashtbl.hash
    let equal = equal_p
    let show (Assign (x, i)) = x ^ "+=" ^ if i then "T" else "F"
  end

  module A : CollectionType with type t = a = struct
    type t = a
    let compare = compare_a
    let hash = Hashtbl.hash
    let equal = equal_a
    let show = function Bool (x, v) -> x ^ "=" ^ if v then "T" else "F"
  end

  let variable = get_name_p

  let variable_test = get_name_a

  let get_bool s = 
    match s with
    | "T" -> true
    | "F" -> false
    | _ -> failwith ("invalid boolean value: " ^ s)


  let parse name es =
    match (name, es) with
    | "set", [(EId s1); (EId s2)] -> Right (Assign (s1, get_bool s2))
    | "=", [(EId s1); (EId s2)] -> Left (Bool (s1, get_bool s2))
    | _, _ ->
        failwith
          ("Cannot create theory object from (" ^ name ^ ") and parameters")


  open BatSet

  let push_back (Assign (x, i)) a =
    match a with
    | Bool (v, j) when x = v && i <> j -> PSet.create K.Test.compare
    | Bool (v, j) when x = v && i = j ->
        PSet.singleton ~cmp:K.Test.compare (K.one ())
    | _ -> PSet.singleton ~cmp:K.Test.compare (K.theory a)


  let rec subterms x = PSet.singleton ~cmp:K.Test.compare (K.theory x)

  let simplify_and (Bool (x, v1)) (Bool (y, v2)) =
    if x = y && v1 <> v2 then Some (K.zero ()) else None


  let simplify_or (Bool (x, v1)) (Bool (y, v2)) =
    if x = y && v1 <> v2 then Some (K.one ()) else None


  let simplify_not (Bool (x, v)) = Some (K.theory (Bool (x, not v)))

  let merge (p1: P.t) (p2: P.t) : P.t = p2

  let reduce a p = Some p

  let unbounded () = false

  open Z3

  let theory_to_z3_expr (a : A.t) (ctx : Z3.context) (map : Z3.Expr.expr StrMap.t) = 
    match a with Bool (x, v) ->
    let var = StrMap.find x map in
    let value = Z3.Boolean.mk_val ctx v in
    Z3.Boolean.mk_eq ctx var value

  let create_z3_var (str,a) (ctx : Z3.context) (solver : Z3.Solver.solver) : Z3.Expr.expr =
    let sym = Symbol.mk_string ctx str in
    let bool_sort = Z3.Boolean.mk_sort ctx in
    Expr.mk_const ctx sym bool_sort 

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
          | One | Zero | Placeholder _ -> failwith "Increment: satisfiability"
          | Not b -> StrMap.map Range.negate (aux b)
          | PPar (b, c) -> mergeOp (aux b) (aux c) Range.union
          | PSeq (b, c) -> mergeOp (aux b) (aux c) Range.inter
          | Theory Bool (x, true) ->
              StrMap.singleton x (Range.from_range (1, max_int))
          | Theory Bool (x, false) ->
              StrMap.singleton x (Range.from_range (0, 0))
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
