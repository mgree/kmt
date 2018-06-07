open Kat
open Common
open Syntax
open Hashcons
open BatSet


type field_val = 
  | Src of int 
  | Dst of int 
  | Pt of int
  | Sw of int
  [@@deriving eq, ord]

let get_field = function 
  | Src _ -> "src"
  | Dst _ -> "dst"
  | Pt _ -> "pt"
  | Sw _ -> "sw"

let get_value = function 
  | Src i | Dst i | Pt i | Sw i -> i

let hash_fv = function
  | Src i -> 3 * i + 5 
  | Dst i -> 7 * i + 11
  | Pt i -> 13 * i + 17
  | Sw i -> 23 * i + 31

let field_val_of_string s i = 
  match s with 
  | "src" -> Src i 
  | "dst" -> Dst i 
  | "pt" -> Pt i 
  | "sw" -> Sw i 
  | _ -> failwith ("Invalid field value: " ^ s)

let show_field_val sep fv = 
  match fv with 
  | Src i -> "src" ^ sep ^ (string_of_int i)
  | Dst i -> "dst" ^ sep ^ (string_of_int i)
  | Pt i -> "pt" ^ sep ^ (string_of_int i)
  | Sw i -> "sw" ^ sep ^ (string_of_int i)


module rec Network : (THEORY with type A.t = field_val and type P.t = field_val) = struct 
  module K = KAT(Network)

  module Test = K.Test
  module Term = K.Term

  module A : (CollectionType with type t = field_val) = struct 
    type t = field_val
    let compare = compare_field_val
    let equal = equal_field_val
    let hash = hash_fv
    let show = show_field_val "="
  end 

  module P : (CollectionType with type t = field_val) = struct 
    type t = field_val
    let compare = compare_field_val
    let equal = equal_field_val
    let hash = hash_fv
    let show = show_field_val "<-"
  end
  
  let parse name es =
    match name, es with
    | "=", [EId s1; EId s2] -> Left (field_val_of_string s1 (int_of_string s2))
    | "<-", [EId s1; EId s2] -> Right (field_val_of_string s1 (int_of_string s2))
    | _, _ -> failwith ("Cannot create theory object from (" ^ name ^ ") and parameters")

  let rec subterms (a: K.A.t) = PSet.singleton ~cmp:A.compare a

  let rec push_back p a =
    match p, a with 
    | Src i, Src j 
    | Dst i, Dst j 
    | Pt i, Pt j 
    | Sw i, Sw j -> 
        if i = j 
        then PSet.singleton ~cmp:K.Test.compare (K.one()) 
        else PSet.create K.Test.compare
    | _, _ -> PSet.singleton ~cmp:K.Test.compare (K.theory a)

  let merge x y = y

  let reduce a p = 
    if equal_field_val a p then None 
    else Some p

  let unbounded () = false

  let subterms x = failwith ""

  let variable x = get_field x

  let satisfiable x = failwith ""

  let simplify_and x y = 
    match x,y with 
    | Src a, Src b 
    | Dst a, Dst b
    | Pt a, Pt b 
    | Sw a, Sw b -> Some (if a = b then K.theory x else K.zero ())
    | _, _ -> None

  let simplify_or x y = None 

  let simplify_not x = None

end