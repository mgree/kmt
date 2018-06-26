open Kat 
open Syntax
open Common
open Hashcons
open Range

type a = 
  | Lt of string * int
  | Gt of string * int
  [@@deriving eq]

type p = 
  | Increment of string * int
  [@@deriving eq]

let get_name_a = function 
  | Lt(x,_) -> x 
  | Gt(x,_) -> x

let get_name_p (Increment(x,_)) = x

let get_value = function 
  | Lt(_,v) -> v
  | Gt(_,v) -> v

let to_int = function 
  | Lt _ -> 0 
  | Gt _ -> 1

let compare_a a b = 
  let cmp = StrType.compare (get_name_a a) (get_name_a b) in 
  if cmp <> 0 then cmp 
  else 
    let cmp = get_value a - get_value b in 
    if cmp <> 0 then cmp else to_int a - to_int b  

let compare_p p q = 
  match p,q with 
  | Increment(x,i), Increment(y,j) -> 
    let cmp = StrType.compare x y in 
    if cmp <> 0 then cmp else i - j 

module rec Addition : (THEORY with type A.t = a and type P.t = p) = struct
  module K = KAT(Addition)

  module Test = K.Test
  module Term = K.Term

  module P : (CollectionType with type t = p) = struct 
    type t = p
    let compare = compare 
    let hash = Hashtbl.hash
    let equal = equal_p
    let show (Increment(x,i)) = x ^ "+=" ^ string_of_int i
  end

  module A : (CollectionType with type t = a) = struct 
    type t = a 
    let compare = compare_a
    let hash = Hashtbl.hash 
    let equal = equal_a
    let show = function 
      | Lt (x,v) -> x ^ "<" ^ (string_of_int v)
      | Gt (x,v) -> x ^ ">" ^ (string_of_int v)
  end

  let variable = get_name_p
  
  let parse name es =
    match name, es with
    | "inc", [EId s1; EId s2] -> Right (Increment(s1, int_of_string s2))
    | ">", [EId s1; EId s2] -> Left (Gt (s1, int_of_string s2))
    | "<", [EId s1; EId s2] -> Left (Lt (s1, int_of_string s2))
    | _, _ -> failwith ("Cannot create theory object from (" ^ name ^ ") and parameters")

  open BatSet

  let push_back (Increment(x,i)) a = 
    match a with 
    | Lt (_,j) when i >= j -> PSet.create K.Test.compare
    | Gt (_,j) when i > j -> PSet.singleton ~cmp:K.Test.compare (K.one())
    | Lt (y,j) when x = y -> PSet.singleton ~cmp:K.Test.compare (K.theory (Lt (y,j-i)))
    | Gt (y,j) when x = y -> PSet.singleton ~cmp:K.Test.compare (K.theory (Gt (y,j-i)))
    | _ -> PSet.singleton ~cmp:K.Test.compare (K.theory a)

  let rec subterms x = 
    match x with 
    | Lt(_,0) | Gt(_,0) -> PSet.singleton ~cmp:K.Test.compare (K.theory x)
    | Lt(v,i) -> PSet.add (K.theory x) (subterms (Lt(v,i-1)))
    | Gt(v,i) -> PSet.add (K.theory x) (subterms (Gt(v,i-1)))

  let simplify_and a b = 
    match a,b with 
    | Gt(x,v1), Gt(y,v2) when x = y -> Some (K.theory (Gt(x, max v1 v2)))
    | Lt(x,v1), Lt(y,v2) when x = y -> Some (K.theory (Lt(x, min v1 v2)))
    | Gt(x,v1), Lt(y,v2)
    | Lt(y,v2), Gt(x,v1) when x = y && v2 <= v1 -> Some (K.zero())
    | _, _ -> None

  let simplify_not a =
    match a with 
    | Gt(x,v) -> Some (K.theory (Lt(x,v+1)))
    | Lt(x,0) -> Some (K.one())
    | Lt(x,v) -> Some (K.theory (Gt(x,v-1)))
 
  let simplify_or a b = None

  let merge (p1 : P.t) (p2 : P.t) : P.t = 
    match p1, p2 with
    | Increment(x,i), Increment(y,j) -> Increment(x,i+j)

  let reduce a p = Some p

  let unbounded () = true

  open Z3

  let rec all_variables (a : K.Test.t) : StrSet.t = 
    match a.node with 
    | One | Zero | Placeholder _ -> StrSet.empty
    | Not b -> all_variables b 
    | PPar(b,c) | PSeq(b,c) -> 
        StrSet.union (all_variables b) (all_variables c)
    | Theory(Gt(x,_)) | Theory(Lt(x,_)) -> StrSet.singleton x

  let sat (a : K.Test.t) = 
    let rec sat_aux (a : K.Test.t) ctx map = 
      match a.node with 
      | One -> Boolean.mk_true ctx
      | Zero -> Boolean.mk_false ctx
      | Not b -> Boolean.mk_not ctx (sat_aux b ctx map)
      | PPar(b,c) -> Boolean.mk_or ctx [sat_aux b ctx map; sat_aux c ctx map]
      | PSeq(b,c) -> Boolean.mk_and ctx [sat_aux b ctx map; sat_aux c ctx map]
      | Placeholder _ -> failwith "sat: unreachable"
      | Theory x -> 
          match x with 
          | Lt(x,v) -> 
              let var = StrMap.find x map in
              let value = Arithmetic.Integer.mk_numeral_i ctx v in
              Arithmetic.mk_lt ctx var value
          | Gt(x,v) ->
              let var = StrMap.find x map in
              let value = Arithmetic.Integer.mk_numeral_i ctx v in
              Arithmetic.mk_gt ctx var value
    in
    (* grab all the referenced variables *)
    let vars = all_variables a in 
    (* Create the solver *)
    let cfg = [("model", "false"); ("proof", "false")] in
    let ctx = (mk_context cfg) in
    let solver = (Solver.mk_solver ctx None) in
    (* create variables from each referenced variable *)
    let map = StrSet.fold (fun str acc ->
      let sym = (Symbol.mk_string ctx str) in
      let int_sort = Arithmetic.Integer.mk_sort ctx in
      let xc = (Expr.mk_const ctx sym int_sort) in
      let is_nat = Arithmetic.mk_ge ctx xc (Arithmetic.Integer.mk_numeral_i ctx 0) in
      Solver.add solver [is_nat];
      StrMap.add str xc acc
    ) vars StrMap.empty in
    (* recrusively generate the formula and assert it *)
    let formula = sat_aux a ctx map in 
    Solver.add solver [formula];   
    let status = Solver.check solver [] in
    Solver.reset solver;
    status = Solver.SATISFIABLE

  module H = Hashtbl.Make(K.Test)
  let tbl = H.create 2048

  let rec can_use_fast_solver (a : K.Test.t) = 
    match a.node with 
    | One | Zero | Placeholder _ | Theory _ -> true
    | PPar _ -> false
    | PSeq(b,c) -> can_use_fast_solver b && can_use_fast_solver c 
    | Not ({node=Theory _}) -> true 
    | Not (_) -> false

  let satisfiable  (a : K.Test.t) =
    try H.find tbl a 
    with _ ->
    (* Printf.printf "Checking Sat %s\n" (K.Test.show a); *)

    debug (fun () -> Printf.printf "SAT: %s" (K.Test.show a));

    if not (can_use_fast_solver a) then
      (
      debug (fun () -> Printf.printf " SLOW\n");
      let ret = sat a in
      H.add tbl a ret;
      ret)
    else
      (
      debug (fun () -> Printf.printf " FAST\n");
      let mergeOp map1 map2 op = 
          StrMap.merge (fun _ v1 v2 -> 
            match v1,v2 with 
            | None, _ -> v2
            | _, None -> v1 
            | Some x, Some y -> Some (op x y)
          ) map1 map2
      in
      let rec aux (a : K.Test.t) : Range.t StrMap.t = 
        match a.node with 
        | One | Zero | Placeholder _ -> failwith "Increment: satisfiability"
        | Not b -> StrMap.map Range.negate (aux b)
        | PPar(b,c) -> mergeOp (aux b) (aux c) Range.union
        | PSeq(b,c) -> mergeOp (aux b) (aux c) Range.inter
        | Theory(Gt(x,v)) -> StrMap.singleton x (Range.from_range (v+1,max_int))
        | Theory(Lt(x,v)) -> 
            let p = (if v = 0 then Range.bot else Range.from_range (0,v-1)) in
            StrMap.singleton x p
      in
      match a.node with 
      | One -> true
      | Zero -> false
      | _ -> 
          let result = aux a in           
          let ret = StrMap.for_all (fun _ r -> not (Range.is_false r)) result in 
          (* Printf.printf "Actual Result: %b\n" ret; *)
          H.add tbl a ret;
          ret)

end
