type expr = 
  | EZero
  | EOne
  | EId of string
  | ETheory of string * expr list
  | EPar of expr * expr
  | ESeq of expr * expr 
  | EStar of expr
  | ENot of expr 

let rec expr_to_string e = 
  match e with 
  | EZero -> "0"
  | EOne -> "1"
  | EId s -> "id(" ^ s ^ ")"
  | EPar(e1,e2) -> "(" ^ expr_to_string e1 ^ " + " ^ expr_to_string e2 ^ ")"
  | ESeq(e1,e2) -> expr_to_string e1 ^ ";" ^ expr_to_string e2
  | EStar e1 -> "(" ^ expr_to_string e1 ^ ")*"
  | ENot e1 -> "-" ^ expr_to_string e1
  | ETheory(name, es) -> name ^ "(..)"