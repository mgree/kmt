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

  let subterms x = failwith ""

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

  let satisfiable  (a : K.Test.t) = failwith "Not implemented"

end
