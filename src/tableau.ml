open Batteries;;
include BatSet;;
include BatMap;;
include Format;;
include String;;
  

(*  LTL SYNTAX, full *)
module LTL = struct
  
  type 'a ltl =  F
               | T
               | P of 'a
               | Imp of 'a ltl * 'a ltl
               | And of 'a ltl * 'a ltl
               | Or of 'a ltl * 'a ltl
               | Not of 'a ltl
               | WX of 'a ltl
               | X of 'a ltl
               | E of 'a ltl
               | G of 'a ltl
               | W of 'a ltl * 'a ltl
               | U of 'a ltl * 'a ltl

  ;;

  (* Pretty printer *)
  let rec stringPrec prec phi =
    match (prec,phi) with
      (0,U(a,b))   -> "(" ^ stringPrec 1 a ^ ") U (" ^ stringPrec 0 b ^ ")"
    | (0,W(a,b))   -> "(" ^ stringPrec 1 a ^ ") W (" ^ stringPrec 0 b ^ ")"
    | (0,x)        -> stringPrec 1 x
    | (1,Not(X T)) -> "end"
    | (1,Not a)    -> " ~" ^ stringPrec 2 a                    
    | (1,WX a)     -> "WX " ^ stringPrec 2 a
    | (1,E a)      -> "E " ^ stringPrec 2 a
    | (1,And(a,b)) -> stringPrec 2 a ^ " & " ^ stringPrec 2 b
    | (1,Or(a,b))  -> stringPrec 2 a ^ " + " ^ stringPrec 2 b
    | (1,Imp(a,b)) -> stringPrec 2 a ^ " -> " ^ stringPrec 2 b
    | (1,x)        -> stringPrec 2 x
    | (2,T)        -> "T"
    | (2,F)        -> "F"
    | (2,Not(X T)) -> "end"
    | (2,Not a)    -> " ~" ^ stringPrec 2 a
    | (2,WX a)     -> "WX " ^ stringPrec 2 a
    | (2,X a)      -> "X " ^ stringPrec 2 a
    | (2,E a)      -> "E " ^ stringPrec 2 a
    | (2,G a)      -> "G " ^ stringPrec 2 a
    | (2,P v)      -> v         (* ONLY ACCEPTS STRINGS AS VARS *)
    | (_,x)        -> "(" ^ stringPrec 0 x ^ ")"           
  ;;
  let stringify phi = stringPrec 0 phi;;

  (* The End Of Time Sugar *)
  let start = Not (X T);; 
    
  (* Helper Functions to determine type of function *)
  let isProp phi =
    match phi with
      (P _ ) -> true
    | _ -> false
  ;;
  let isPrim phi =
    match phi with
      T -> true
    | F -> true
    | (P _) -> true
    | _ -> false
  ;;
  let isImp phi =
    match phi with
      (Imp(x,y)) -> true
    | _ -> false
  ;;
  let isAnd phi =
    match phi with
      And(x,y) -> true
    | _ -> false
  ;;
  let isOr phi =
    match phi with
      Or(x,y) -> true
    | _ -> false
  ;;
  let isNot phi =
    match phi with
      (Not x) -> true
    | _ -> false
  ;;
  let isX phi =
    match phi with
      (X x) -> true
    | _ -> false
  ;;
  let isWX phi =
    match phi with
      (WX x) -> true
    | _ -> false
  ;;
  let isG phi =
    match phi with
      (G x) -> true
    | _ -> false
  ;;
  let isE phi =
    match phi with
      (E x) -> true
    | _ -> false
  ;;
  let isW phi =
    match phi with
      W(x,y) -> true
    | _ -> false
  ;;
  let isU phi =
    match phi with
      U(x,y) -> true
    | _ -> false
  ;;
  let isClass phi =
    match phi with
      F -> true
    | T -> true
    | Imp(_,_) -> true
    | And(_,_) -> true
    | Or(_,_) -> true
    | Not _ -> true
    | _ -> false
  ;;
  let isTemporal phi =
    match phi with
      WX _ -> true
    | X _ -> true
    | E _ -> true
    | G _ -> true
    | U(_,_) -> true
    | W(_,_) -> true
    | _ -> false
  ;;

  (*End paritioning helper functions*)

  (*Compare to allow sets*)
  let compare = Pervasives.compare;; 

  (* Convert temporal formulae to nontemporal *)
  let rec dropTemporal phi =
    match phi with
      F -> F
    | T -> T
    | X _ -> F
    | WX _ -> T
    | P a -> P a
    | W(a,b) -> Or (dropTemporal a, dropTemporal b)
    | U(_,b) -> dropTemporal b
    | Imp(a,b) -> Imp (dropTemporal a, dropTemporal b)
    | Or(a,b) -> Or (dropTemporal a, dropTemporal b)
    | And(a,b) -> And (dropTemporal a, dropTemporal b)
    | Not a -> Not (dropTemporal a)
    | E a -> dropTemporal a
    | G a -> dropTemporal a
  ;;
end;; (* /LTL *)
  
  (* Positive-negative pairs (PNPs) and tableaux *)



module PNP = struct
  type pnptype = Norm | Temp | Term;; (* Dont really need temp unless graphics? *)
  let tstring t =
    match t with
      Norm -> "Norm"
    | Temp -> "Temp"
    | Term -> "Term"
  ;;
    

    
  type 'a pnp = {typ : pnptype; pos : ('a LTL.ltl) BatSet.t; neg : ('a LTL.ltl) BatSet.t};;

    
  let setString s =
    "{" ^ BatSet.fold (fun phi rst -> LTL.stringify phi ^ "," ^ rst) s "}"
  ;;
    
      
    
  let stringify p =
    "(" ^ tstring(p.typ) ^ ": " ^ setString(p.pos) ^ ", " ^ setString(p.neg) ^ "})"
  ;;
    

    
  let compare = Pervasives.compare;;
    
  let terminal q = { typ=Term;
                     pos=BatSet.map LTL.dropTemporal q.pos;
                     neg=BatSet.add (LTL.X LTL.T) (BatSet.map LTL.dropTemporal q.neg);
                   };;

  let pairPSat propSat formPair rst =
    match formPair with
      (LTL.P a, LTL.P b ) -> propSat a b && rst
    | (_ , _ ) -> true && rst
  ;;
    
                                       
    
  let closed propSat p =
    let prod = BatSet.cartesian_product p.pos p.neg in
    not (BatSet.fold (pairPSat propSat) prod true)
    || BatSet.mem LTL.F p.pos
    || BatSet.mem LTL.T p.neg
  ;;

  let isTerminal p = p.typ == Term ;;

  let typProp t =
    match t with
      Norm -> Norm
    | Temp -> Norm
    | Term -> Term
  ;;

  let update oldT newP newN = {typ=typProp oldT; pos=newP; neg=newN;} ;;
   
  exception Unexpected_Identifier;;

  let satisfying pred s =
    let (sat, unsat) = BatSet.partition pred s in
    if BatSet.is_empty sat
    then None
    else
      let (v,sat') = BatSet.pop_max sat in
      Some (v, BatSet.union sat' unsat)
  ;;
    
  (* get all formulae underneath X operators *)
  let getXs s = BatSet.filter_map
                (fun f ->
                  match f with
                    (LTL.X a) -> Some a
                  | _         -> None
                ) s
  ;;
  (* The sigma functions from thesis *)
  let sigma_one p = getXs (p.pos) ;;
  let sigma_two p = BatSet.filter
                      (fun f ->
                        match f with
                          LTL.W(_,b) -> BatSet.mem b p.neg
                        | _           -> false
                      ) (p.pos)
  ;;
  let sigma_three p = BatSet.filter
                        (fun f ->
                          match f with
                            LTL.W(a,_) -> BatSet.mem (LTL.X LTL.T) p.neg &&
                                            BatSet.mem a p.pos
                          | _           -> false
                        ) (p.pos)
  ;;
  let sigma_four p = getXs p.neg;;
  let sigma_five p = BatSet.filter
                       (fun f ->
                         match f with
                           LTL.W(a,b) -> BatSet.mem a p.pos ||
                                           BatSet.mem b p.neg 
                         | _           -> false
                       ) (p.neg)
  ;;
  let sigma p = { typ=p.typ;
                  pos=BatSet.union (BatSet.union (sigma_one p) (sigma_two p)) (sigma_three p);
                  neg=BatSet.union (sigma_four p) (sigma_five p);
                }
  ;;
        
  (* Find the successors of a node in a tableau *)
  let makeSucc propSat q =
    if closed propSat q
    then []         (* BOT *)
    else
      (match satisfying LTL.isImp q.pos with (* ->+ *)
        Some (LTL.Imp(a,b), newPos) ->
        [ update q.typ (BatSet.add b newPos) (q.neg) ;
          update q.typ newPos (BatSet.add a q.neg)
        ]
      | Some _ -> raise Unexpected_Identifier
      | None ->
         (match satisfying LTL.isImp q.neg with (* ->- *)
           Some (LTL.Imp(a,b), newNeg) ->
           [ update q.typ (BatSet.add a q.pos) (BatSet.add b newNeg)]
         | Some _ -> raise Unexpected_Identifier
         | None ->
            (match satisfying LTL.isAnd q.pos with (* &&+ *)
              Some (LTL.And(a,b), newPos) ->
              [ update q.typ (BatSet.add a (BatSet.add b newPos)) q.neg]
            | Some _ -> raise Unexpected_Identifier
            | None ->
               (match satisfying LTL.isAnd q.neg with (* &&- *)
                 Some (LTL.And(a,b), newNeg) ->
                 [ update q.typ q.pos (BatSet.add a newNeg);
                   update q.typ q.pos (BatSet.add b newNeg)
                 ]
               | Some _ -> raise Unexpected_Identifier
               | None ->
                  (match satisfying LTL.isOr q.pos with (* ||+ *)
                    Some (LTL.Or(a,b), newPos) ->
                    [ update q.typ (BatSet.add a newPos) q.neg;
                      update q.typ (BatSet.add b newPos) q.neg
                    ]
                  | Some _ -> raise Unexpected_Identifier
                  | None ->
                     (match satisfying LTL.isOr q.neg with (* ||- *)
                       Some (LTL.Or(a,b), newNeg) ->
                       [ update q.typ q.pos (BatSet.add a (BatSet.add b newNeg)) ]
                       
                     | Some _ -> raise Unexpected_Identifier
                     | None ->
                        (match satisfying LTL.isNot q.pos with (* ~+ *)
                          Some (LTL.Not a, newPos) ->
                          [ update q.typ newPos (BatSet.add a q.neg)]
                        | Some _ -> raise Unexpected_Identifier
                        | None ->
                           (match satisfying LTL.isNot q.neg with (* ~- *)
                             Some (LTL.Not a, newNeg) ->
                             [ update q.typ (BatSet.add a q.pos) newNeg ]
                           | Some _ -> raise Unexpected_Identifier
                           | None ->
                              (match satisfying LTL.isG q.pos with (* G+ *)
                                Some (LTL.G a, newPos) ->
                                [update q.typ (BatSet.add a (BatSet.add (LTL.WX(LTL.G a)) newPos)) q.neg]
                              | Some _ -> raise Unexpected_Identifier
                              | None ->
                                 (match satisfying LTL.isG q.neg with
                                   Some (LTL.G a, newNeg) ->
                                   [ update q.typ q.pos (BatSet.add a newNeg);
                                     update q.typ (BatSet.add (LTL.X (LTL.Not (LTL.G a))) q.pos) (newNeg)
                                   ]
                                 | Some _ -> raise Unexpected_Identifier
                                 | None ->
                                    (match satisfying LTL.isE q.pos with
                                      Some (LTL.E a, newPos) ->
                                      [ update q.typ (BatSet.add a newPos) q.neg;
                                        update q.typ (BatSet.add (LTL.X(LTL.E a)) newPos) q.neg
                                      ]
                                    | Some _ -> raise Unexpected_Identifier
                                    | None ->
                                       (match satisfying LTL.isE q.neg with
                                         Some (LTL.E a, newNeg) ->
                                         [ update q.typ q.pos (BatSet.add a (BatSet.add (LTL.X(LTL.E a)) newNeg)) ]
                                       | Some _ -> raise Unexpected_Identifier
                                       | None ->
                                          (match satisfying LTL.isW q.pos with
                                            Some (LTL.W(a,b), newPos) ->
                                            [ update q.typ (BatSet.add a (BatSet.add b newPos)) q.neg;
                                              update q.typ (BatSet.add a (BatSet.add (LTL.WX(LTL.W(a,b))) newPos)) q.neg
                                            ]
                                          | Some _ -> raise Unexpected_Identifier
                                          | None ->
                                             (match satisfying LTL.isW q.neg with
                                               Some (LTL.W(a,b), newNeg) ->
                                               [ update q.typ q.pos (BatSet.add a (BatSet.add b newNeg));
                                                 update q.typ (BatSet.add (LTL.X(LTL.Not(LTL.W(a,b)))) q.pos)
                                                        (BatSet.add b newNeg)
                                               ]
                                             | Some _ -> raise Unexpected_Identifier
                                             | None ->
                                                (match satisfying LTL.isU q.pos with
                                                  Some (LTL.U(a,b), newPos) ->
                                                  [update q.typ (BatSet.add b newPos) q.neg;
                                                   update q.typ (BatSet.add a (BatSet.add (LTL.X(LTL.U(a,b))) newPos)) q.neg
                                                  ]
                                                | Some _ -> raise Unexpected_Identifier
                                                | None ->
                                                   (match satisfying LTL.isU q.neg with
                                                     Some (LTL.U(a,b), newNeg) ->
                                                     [ update q.typ q.pos (BatSet.add a (BatSet.add b newNeg));
                                                       update q.typ q.pos (BatSet.add b (BatSet.add (LTL.X(LTL.U(a,b))) newNeg))
                                                     ]
                                                   | Some _ -> raise Unexpected_Identifier
                                                   | None ->
                                                      (match satisfying LTL.isWX q.pos with
                                                        Some (LTL.WX a, newPos) ->
                                                        [ update q.typ newPos (BatSet.add (LTL.X(LTL.Not a)) q.neg) ]
                                                      | Some _ -> raise Unexpected_Identifier
                                                      | None ->
                                                         (match satisfying LTL.isWX q.neg with
                                                           Some (LTL.WX a, newNeg) ->
                                                           [update q.typ (BatSet.add (LTL.X(LTL.Not a)) q.pos) newNeg]
                                                         | Some _ -> raise Unexpected_Identifier
                                                         | None ->
                                                            let newPos = sigma_one q in
                                                            if BatSet.mem (LTL.X LTL.T) q.neg && BatSet.is_empty newPos
                                                            then [terminal q]
                                                            else [{typ=Temp;
                                                                   pos=newPos;
                                                                   neg=(sigma_four q);}
                                                                 ]))))))))))))))))))
  ;;
        
end;; (* / PNPs *)

module Tableau = struct
  (*Type Alias for tableau *)
  type 'a tableau = ('a PNP.pnp, ('a PNP.pnp) list) BatMap.t;;

  (* For numerical system should return true when a & ~ b is sat 
   * a & ~ b == ~ (~ a + ~~ b) == ~(a -> b)
   *  propSat a b = Nums.sat (a Nums.and (Nums.not B))
   * 
   * The following instance is a placeholder for a functorized version.
   *
   * All occurences of this function in this file use the name
   * propSat. It is passed to the PNP.makeSucc function and the
   * PNP.closed function. 
   *)
  let propSat a b = a <> b;;

  (* An empty tableau *)
  let empty = BatMap.empty;;

  (* Returns true if p has not been added to the keys of t *)
  let unseen t p = not (BatMap.mem p t);;

  (* Adds the list succs as successors of p in t  *)
  let addEdges p succs t = BatMap.add p succs t;;

  (* gets the successors of p in t *)
  let successors p t = if BatMap.mem p t
                       then BatMap.find p t
                       else []
  ;;

  (*Turns a list of successors into a string*)
  let stringSuccs ss =
    match ss with
      [] -> "NO SUCCESSORS"
    | _ -> List.fold_right (fun node rst -> "\n\t" ^ PNP.stringify node ^ rst ) ss "\n"  

  (*Turns a tableau into a string*)
  let stringify tabl =
    let keys = BatMap.keys tabl in
    BatEnum.fold
      (fun rst node->
        let succs = BatMap.find node tabl in
        "\nNODE: " ^ PNP.stringify node ^ stringSuccs succs ^ rst
      ) "" keys

  (* Builds the root PNP for a formula phi *)
  let buildRoot phi = { PNP.typ=PNP.Norm;
                        PNP.pos=BatSet.add phi (BatSet.add (LTL.E LTL.start) BatSet.empty);
                        PNP.neg=BatSet.empty};;

  (* takes the union of two tableaux *)
  let union = BatMap.union ;;

  (*Uses succRule to build a tableau tabl given a worklist of nodes*)
  let rec build succRule worklist tabl =
    match worklist with
      []             -> tabl
    | p :: worklist' ->
       let succs = succRule p in
       let tabl'    = addEdges p succs tabl in
       let newNodes = List.find_all (unseen tabl) succs in
       build succRule (worklist' @ newNodes) tabl'
  ;;

  (* called tableau in Tableau.hs *)
  (* Builds a tableau from an input pnp phi *)
  let from_ltl phi = build (PNP.makeSucc propSat) [buildRoot phi] empty;;

  (* find a terminal path in tabl from the current node p leaving out seen nodes *)
  let rec terminalPath tabl seen p =
    if PNP.closed propSat p then None
    else if BatSet.mem p seen then None
    else if PNP.isTerminal p then Some [p]    
    else
      let succs = successors p tabl in
      let paths = List.filter_map (terminalPath tabl (BatSet.add p seen)) succs in
      (match paths with
        [] -> None
      | (path :: _) -> Some (p::path))
  ;;

  (* find a terminal path in the tableau constructed from phi *)
  let path phi = terminalPath (from_ltl phi) BatSet.empty (buildRoot phi);;

  (* determine if phi is valid*)
  let valid phi = Option.is_none (path (LTL.Not phi));;

  (*Determine if the implication phi -> psi is valid*)
  let implies phi psi = valid (LTL.Imp(phi,psi));;
      
end;;

(*testing stuff*)
let boolstr b = if b then "true" else "false" ;;
let eqstr a b = if a = b then "ok" else "FAILED";;
let teststr a b = a ^ " = " ^ boolstr b ^ " : " ^ eqstr a (boolstr b);;
let testv expect phi = print_endline (teststr expect (Tableau.valid phi));;
let test expect a b  = print_endline (teststr expect (Tableau.implies a b));;
  
let a = LTL.P "a" ;;
let b = LTL.P "b" ;;

(* tests *)
let main () =
  print_endline "\n----------------------------------------------------";
  print_endline "  DECISION PROCEDURE TESTS (<expected> = <actual>)";
  print_endline "----------------------------------------------------";
  test "true" (LTL.And(LTL.E(a), LTL.start)) (a);
  test "false" a b;
  test "true" (LTL.X (LTL.Imp(a,b))) (LTL.Imp(LTL.X a, LTL.X b)); 
  test "false" (LTL.Imp(LTL.X a, LTL.X b)) (LTL.X (LTL.Imp(a,b))); 
  test "true" (LTL.start) (LTL.Not (LTL.X a));                    
  test "true" (LTL.W(a,b)) (LTL.Or(b,(LTL.And(a,LTL.WX(LTL.W(a,b)))))); 
  test "true" (LTL.Or(b,(LTL.And(a,LTL.WX(LTL.W(a,b)))))) (LTL.W(a,b)); 
  test "true" (LTL.And(LTL.G(LTL.Imp(a,b)), LTL.G(LTL.Imp(a,LTL.WX a)))) (LTL.Imp(a,LTL.G b));
  test "true" (LTL.Imp(LTL.X a, LTL.X b)) (LTL.Or(LTL.start,LTL.X(LTL.Imp(a,b))));
  testv "true" (LTL.Not(LTL.And(
                            LTL.And(
                                LTL.And(LTL.E a,
                                        LTL.G(LTL.Imp(a,LTL.E b))),
                                LTL.G(LTL.Imp(b,LTL.E a))),
                            LTL.G(LTL.Or(LTL.Not a, LTL.Not b)))))
;;

  
main() ;;
