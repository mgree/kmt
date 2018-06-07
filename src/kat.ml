open Syntax 
open Common
open Hashcons

let merge = true

type 'a pred = 'a pred_hons hash_consed
and 'a pred_hons =
  | Placeholder of int
  | Theory of 'a
  | Zero
  | One
  | Not of 'a pred
  | PPar of 'a pred * 'a pred
  | PSeq of 'a pred * 'a pred

type ('a,'p) kat = ('a,'p) kat_hons hash_consed
and ('a,'p) kat_hons =
  | Action of int * 'p
  | Pred of 'a pred
  | Par of ('a,'p) kat * ('a,'p) kat
  | Seq of ('a,'p) kat * ('a,'p) kat
  | Star of ('a,'p) kat

module type KAT_IMPL = sig
  module A : CollectionType 
  module P : CollectionType
  module Test : (CollectionType with type t = A.t pred)
  module Term : (CollectionType with type t = (A.t, P.t) kat)
  (* Theory functions *)
  val push_back : P.t -> A.t -> Test.t BatSet.PSet.t
  val push_back_test : P.t -> Test.t -> Test.t BatSet.PSet.t
  val satisfiable : Test.t -> bool
  val unbounded : unit -> bool
  val implies : Test.t -> Test.t -> bool
  (* Smart constructors *)
  val placeholder : int -> Test.t
  val theory : A.t -> Test.t
  val zero : unit -> Test.t 
  val one : unit -> Test.t 
  val not : Test.t -> Test.t
  val ppar : Test.t -> Test.t -> Test.t 
  val pseq : Test.t -> Test.t -> Test.t 
  val action : P.t -> Term.t
  val pred : Test.t -> Term.t 
  val par : Term.t -> Term.t -> Term.t
  val seq : Term.t -> Term.t -> Term.t
  val star : Term.t -> Term.t
  (* Utility functions *)
  val subterms : Test.t -> Test.t BatSet.PSet.t
  val test_of_expr : Syntax.expr -> Test.t
  val term_of_expr : Syntax.expr -> Term.t
  val parse : string -> Term.t
end

module type THEORY = sig
  module A : CollectionType
  module P : CollectionType
  module Test : (CollectionType with type t = A.t pred)
  module Term : (CollectionType with type t = (A.t,P.t) kat)
  module K : KAT_IMPL with module A = A and module P = P and module Test = Test and module Term = Term
  val parse : string -> expr list -> (A.t, P.t) either
  val push_back : P.t -> A.t -> Test.t BatSet.PSet.t
  val subterms : A.t -> Test.t BatSet.PSet.t
  val simplify_not : A.t -> Test.t option
  val simplify_and : A.t -> A.t -> Test.t option 
  val simplify_or  : A.t -> A.t -> Test.t option
  val merge : P.t -> P.t -> P.t
  val reduce : A.t -> P.t -> P.t option
  val variable : P.t -> string
  val unbounded : unit -> bool
  val satisfiable : Test.t -> bool
end


module KAT(T : THEORY) : (KAT_IMPL with module A = T.A and module P = T.P) = struct
  type test = T.A.t pred
  type term = (T.A.t, T.P.t) kat

  module A = T.A 
  module P = T.P

  let rec show_test a = show_test_hons a.node
  and show_test_hons a = 
    match a with 
    | Placeholder i -> "placeholder(" ^ (string_of_int i) ^ ")"
    | Theory t ->  T.A.show t
    | Zero -> "false"
    | One -> "true"
    | Not a -> "not(" ^ show_test a ^ ")"
    | PPar (a1, a2) -> "(" ^ (show_test a1) ^ " + " ^ (show_test a2) ^ ")"
    | PSeq (a1, a2) -> "(" ^ (show_test a1) ^ ";" ^ (show_test a2) ^ ")"

  and show_term p = 
    match p.node with 
    | Action (_,p) -> T.P.show p
    | Pred a -> show_test a
    | Par(p1,p2) -> "(" ^ (show_term p1) ^ " + " ^ (show_term p2) ^ ")"
    | Seq(p1,p2) -> (show_term p1) ^ ";" ^ (show_term p2)
    | Star p1 -> "(" ^ (show_term p1) ^ ")*"

  let equal_pred x y =
    match x, y with 
    | Theory a, Theory b -> T.A.equal a b
    | Zero, Zero -> true
    | One, One -> true
    | Not a, Not b -> a.tag = b.tag 
    | PPar(a,b), PPar(c,d) | PSeq(a,b), PSeq(c,d) -> 
        (a.tag = c.tag && b.tag = d.tag)
    | _, _ -> false

  let hash_pred x = 
    let ret = match x with
    | Placeholder i -> i
    | Theory a -> 2 + T.A.hash a
    | Zero -> 3
    | One -> 5
    | Not a -> 7 * a.hkey + 11
    | PPar(a,b) -> 13 * (b.hkey + (17 * a.hkey + 7))
    | PSeq(a,b) -> 23 * (b.hkey + (31 * a.hkey + 11)) in 
    ret

  module Test : (CollectionType with type t = T.A.t pred) = struct 
    type t = T.A.t pred
    let equal x y = x.tag = y.tag
    let compare x y = x.tag - y.tag  
    let hash x = x.hkey
    let show = show_test
  end

  let equal_kat x y =
    match x, y with 
    | Action (_,a), Action (_,b) -> T.P.equal a b
    | Pred a, Pred b -> a.tag = b.tag
    | Par(a,b), Par(c,d) | Seq(a,b), Seq(c,d) -> 
        (a.tag = c.tag && b.tag = d.tag)
    | Star a, Star b -> a.tag = b.tag
    | _, _ -> false

  let hash_kat x = 
    match x with 
    | Action (_,a) -> 2 + T.P.hash a
    | Pred a -> 3 + Test.hash a
    | Par(a,b) -> 31 * (b.hkey + (31 * a.hkey + 5))
    | Seq(a,b) -> 31 * (b.hkey + (31 * a.hkey + 7))
    | Star a -> 31 * a.hkey + 11

  module Term : (CollectionType with type t = (T.A.t, T.P.t) kat) = struct 
    type t = (T.A.t, T.P.t) kat
    let equal x y = x.tag = y.tag
    let compare x y = x.tag - y.tag 
    let hash x = x.hkey
    let show = show_term
  end

  let tbl_pred = Hashcons.create 8
  let tbl_kat = Hashcons.create 8

  let hashcons_pred = Hashcons.hashcons hash_pred equal_pred tbl_pred
  let hashcons_kat  = Hashcons.hashcons hash_kat equal_kat tbl_kat

  let theory x = hashcons_pred (Theory x)
  let zero () = hashcons_pred Zero
  let one () = hashcons_pred One
  
  let placeholder i = hashcons_pred (Placeholder i)

  let not x = 
    match x.node with 
    | Not y -> y
    | One -> zero () 
    | Zero -> one ()
    | Theory a -> 
        (match T.simplify_not a with 
         | None -> hashcons_pred (Not x)
         | Some t -> t)
    | _ -> hashcons_pred (Not x)

  let ppar x y = 
    match x.node, y.node with
    | _, Zero -> x
    | Zero, _ -> y
    | One, _ -> x 
    | _, One -> y
    | Theory a, Theory b -> 
        (match T.simplify_or a b with 
         | None -> hashcons_pred (PPar (x,y))
         | Some t -> t)
    | _, _ -> hashcons_pred (PPar (x,y))
  
  let c_ord x y = 
    match x.node, y.node with 
    | Theory a, Theory b -> T.A.compare a b
    | _, _ -> x.tag - y.tag

  let rec pseq x y = 
    if x.tag = y.tag then x else
    match x.node, y.node with
    | _, Zero -> y
    | Zero, _ -> x
    | _, One -> x 
    | One, _ -> y
    (* simplify theory expressions if possible *)
    | Theory a, Theory b -> 
        (match T.simplify_and a b with 
         | None -> 
            if Test.compare x y < 0 then hashcons_pred (PSeq (x,y))
            else hashcons_pred (PSeq (y,x))
         | Some t -> t)
    | Theory a, PSeq ({node=Theory d} as b, c) -> 
        (match T.simplify_and a d with 
         | None -> 
            if Test.compare x b > 0 then pseq b (pseq x c)
            else hashcons_pred (PSeq (x,y))
         | Some t -> pseq t c)
    (* rewrite test sequences into semi-canonical form *)
    | PSeq (p,q), PSeq (r,s) when c_ord p s >= 0 -> pseq r (pseq s x)
    | PSeq (p,q), PSeq (r,s) when c_ord p r >= 0 && c_ord q s < 0 -> pseq r (pseq p (pseq q s))
    | PSeq (p,q), PSeq (r,s) when c_ord p r >= 0 && c_ord q s >= 0 -> pseq r (pseq p (pseq s q))
    | PSeq (p,q), PSeq (r,s) when c_ord q s >= 0 -> pseq p (pseq r (pseq s q))
    | PSeq (p,q), PSeq (r,s) when c_ord q r >= 0 -> pseq p (pseq r (pseq q s)) 
    | PSeq (p,q), PSeq (r,s) -> pseq p (pseq q y)
    | _, PSeq (r,s) when x.tag = r.tag || x.tag = s.tag -> y 
    | _, PSeq (r,s) when c_ord x s > 0 -> pseq r (pseq s x)
    | _, PSeq (r,s) when c_ord x r > 0 -> pseq r (pseq x s)
    | _, PSeq (r,s) -> hashcons_pred (PSeq (x,y))
    | PSeq (p,q), _ when y.tag = q.tag || y.tag = p.tag -> x 
    | PSeq (p,q), _ when c_ord y q > 0 -> pseq p (pseq q y)
    | PSeq (p,q), _ when c_ord y p > 0 -> pseq p (pseq y q)
    | PSeq (p,q), _ -> hashcons_pred (PSeq (y,x))
    (* default case *)
    | _, _ ->
      if Test.compare x y < 0 
        then hashcons_pred (PSeq (x,y))
        else hashcons_pred (PSeq (y,x))

  let gen_label = 
    let x = ref 0 in 
    fun () -> x:=!x+1; !x

  let action x = hashcons_kat (Action (gen_label(), x))
  let pred x = hashcons_kat (Pred x)

  let rec par x y =
    if x.tag == y.tag then x else
    match x.node, y.node with 
    | _, Pred {node=Zero} -> x 
    | Pred {node=Zero}, _ -> y
    | Pred a, Pred b -> hashcons_kat (Pred (ppar a b))
    (* write 1 + p;p* as p* *)
    | Pred {node=One}, Seq (p,  ({node=Star q} as r)) when p.tag == q.tag -> r
    | Pred {node=One}, Seq (({node=Star q} as r), p) when p.tag == q.tag -> r
    | Seq (p,  ({node=Star q} as r)), Pred {node=One} when p.tag == q.tag -> r
    | Seq (({node=Star q} as r), p), Pred {node=One} when p.tag == q.tag -> r
    (* rewrite x + ax == x;(1 + a) == x *)
    | Seq ({node=Pred _}, p), _ when p.tag == y.tag -> p 
    | Seq (p, {node=Pred _}), _ when p.tag == y.tag -> p 
    | _, Seq ({node=Pred _}, p) when p.tag == x.tag -> p 
    | _, Seq (p, {node=Pred _}) when p.tag == x.tag -> p 
    | _, _ -> hashcons_kat (Par (x,y))
  
  let rec seq x y = 
    match x.node, y.node with 
    (* merge primitives *)
    | Action (i,p), Action (_,q) when (merge) && (T.variable p == T.variable q) -> 
        hashcons_kat (Action (i, T.merge p q))
    (* identities *)
    | _, Pred {node=Zero} -> y
    | Pred {node=Zero}, _ -> x
    | _, Pred {node=One} -> x 
    | Pred {node=One}, _ -> y
    | Star p, Star q when p.tag == q.tag -> x
    (* rewrite x*; x; x* == x*; x *)
    | Seq ({node=Star p}, q), Star r when q.tag == p.tag && q.tag == r.tag -> x
    | Star r, Seq ({node=Star p}, q) when q.tag == p.tag && q.tag == r.tag -> x
    | Seq ({node=Star p}, q), Seq ({node=Star r}, s) when q.tag == p.tag && q.tag == r.tag -> seq x s
    | Seq (s, {node=Star r}), Seq ({node=Star p}, q) when q.tag == p.tag && q.tag == r.tag -> seq s y
    | _, _ -> hashcons_kat (Seq (x,y))
  
  let star x = 
    match x.node with
    | Pred _ -> pred (one ())
    | Star y -> x
    | _ -> hashcons_kat (Star x)

  open BatSet

  let push_back p a = T.push_back p a

  let rec push_back_test (p : P.t) (test : Test.t) : Test.t PSet.t = 
    match test.node with 
    | One -> PSet.singleton ~cmp:Test.compare test 
    | Zero -> PSet.create Test.compare 
    | Theory x -> T.push_back p x
    | PPar(a,b) -> PSet.union (push_back_test p a) (push_back_test p b)
    | PSeq(a,b) -> 
        let x = push_back_test p a in
        let y = push_back_test p b in 
        let base = PSet.create Test.compare in 
        Common.cross_product x y base pseq
    | Not _ | Placeholder _ -> failwith "Invalid term in pushback"

  let satisfiable x = T.satisfiable x

  let unbounded () = T.unbounded ()

  let implies (a : Test.t) (b : Test.t) : bool =
    let x = pseq a (not b) in
    Pervasives.not (satisfiable x)

  let rec subterms (x : Test.t) : Test.t PSet.t = 
    match x.node with 
    | Zero -> PSet.create Test.compare
    | One -> PSet.singleton ~cmp:Test.compare (one())
    | Theory a -> PSet.union (T.subterms a) (subterms (one()))
    | PPar(a,b) | PSeq(a,b) -> 
        let l = subterms a in
        let r = subterms b in
        PSet.add x (PSet.union l r)
    | Not a -> PSet.add x (subterms a)
    | Placeholder _ -> failwith "Unreachable: subterms"
    
  let rec test_of_exprs name es = 
    match (T.parse name es) with 
    | Left x -> theory x 
    | Right _ -> failwith "Action in predicate"

  and test_of_expr (e : Syntax.expr) : test = 
    match e with 
    | EOne -> one () 
    | EZero -> zero ()
    | EPar(e1,e2) -> ppar (test_of_expr e1) (test_of_expr e2)
    | ESeq(e1,e2) -> pseq (test_of_expr e1) (test_of_expr e2)
    | ENot e1 -> not (test_of_expr e1)
    | EStar _ -> failwith "invalid star inside predicate"
    | EId name -> test_of_exprs name []
    | ETheory(name, es) -> test_of_exprs name es

  and term_of_exprs name es = 
    match T.parse name es with
    | Left x -> pred (theory x)
    | Right x -> action x

  and term_of_expr (e : Syntax.expr) =
    match e with 
    | EOne -> pred (one ())
    | EZero -> pred (zero ())
    | EPar(e1,e2) -> par (term_of_expr e1) (term_of_expr e2) 
    | ESeq(e1,e2) -> seq (term_of_expr e1) (term_of_expr e2)
    | EStar e1 -> star (term_of_expr e1)
    | ENot e1 -> pred (not (test_of_expr e1))
    | EId name -> term_of_exprs name []
    | ETheory(name, es) -> term_of_exprs name es

  let parse s = Input.read_from_str s |> term_of_expr

end