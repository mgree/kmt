open BatSet
open Hashcons
open Common

type letter = int
            
let show_letter l = "pi_" ^ string_of_int l
            
type word = word_hons hash_consed
and word_hons =
  | Emp
  | Eps
  | Ltr of letter
  | Alt of word * word
  | Cat of word * word
  | Str of word

let equal_word x y =
  match (x, y) with
  | Emp, Emp | Eps, Eps -> true
  | Ltr l1, Ltr l2 -> l1 = l2
  | Alt (a, b), Alt (c, d) | Cat (a, b), Cat (c, d) ->
      a.tag = c.tag && b.tag = d.tag
  | Str a, Str b -> a.tag = b.tag
  | _, _ -> false

let hash_word x =
  match x with
  | Emp -> 3
  | Eps -> 5
  | Ltr l -> 7 * l + 3
  | Alt (a, b) -> 13 * (b.hkey + (17 * a.hkey + 19))
  | Cat (a, b) -> 23 * (b.hkey + (29 * a.hkey + 31))
  | Str a -> 37 * a.hkey + 41
         
let tbl_word = Hashcons.create 8

let hashcons_word = Hashcons.hashcons hash_word equal_word tbl_word

let emp = hashcons_word Emp
let eps = hashcons_word Eps
let ltr l = hashcons_word (Ltr l)
let alt w1 w2 =
  match w1.node, w2.node with
  | Emp, _ -> w2
  | _, Emp -> w1
  | _, _ -> if w1.tag = w2.tag
            then w1
            else hashcons_word (Alt (w1, w2))
let cat w1 w2 =
  match w1.node, w2.node with
  | Eps, _ -> w2
  | _, Eps -> w1
  | _, _ -> hashcons_word (Cat (w1, w2))
          
let str w =
  match w.node with
  | Emp -> eps
  | Eps -> eps
  | _ -> hashcons_word (Str w)
  
module Word : CollectionType with type t = word = struct
  type t = word

  let equal x y = x.tag = y.tag
  let compare x y = x.tag - y.tag
  let hash x = x.hkey
  let show : t -> string =
    let rec alt w =
      match w.node with
      | Alt (w1, w2) -> alt w1 ^ " + " ^ alt w2
      | _ -> cat w

    and cat w =
      match w.node with
      | Cat (w1, w2) -> cat w1 ^ " + " ^ cat w2
      | _ -> str w

    and str w =
      match w.node with
      | Str w -> atom w ^ "*"
      | _ -> atom w

    and atom w =
      match w.node with
      | Ltr l -> show_letter l
      | Emp -> "false"
      | Eps -> "true"
      | _ -> "(" ^ alt w ^ " )"
    in
    alt
end

let rec accepting (w: word) : bool =
  match w.node with
  | Eps -> true
  | Str _ -> true
  | Emp | Ltr _ -> false
  | Alt (w1, w2) -> accepting w1 || accepting w2
  | Cat (w1, w2) -> accepting w1 && accepting w2

let rec derivative (w: word) (l: letter) : word option =
  match w.node with
  | Emp -> None
  | Eps -> None
  | Ltr l' -> if l = l' then Some eps else None
  | Alt (w1, w2) ->
     begin match derivative w1 l, derivative w2 l with
     | Some w1', Some w2' -> Some (alt w1' w2')
     | Some w1', None     -> Some w1'
     | None,     Some w2' -> Some w2'
     | _, _ -> None
     end
  | Cat (w1, w2) ->
     begin match derivative w1 l, derivative w2 l with
     | Some w1', Some w2' -> Some (alt (cat w1' w2) (if accepting w1 then w2' else emp))
     | Some w1', None     -> Some (cat w1' w2)
     | None,     Some w2' -> if accepting w1 then Some w2' else None
     | None,     None     -> None
     end
  | Str w_inner ->
     begin match derivative w_inner l with
     | Some w_inner' -> Some (cat w_inner' w)
     | None -> None
     end

module UF = BatUref
module WordMap = Hashtbl.Make(Word)
type state = word UF.uref

let find_state (m: state WordMap.t) (w: word) : state =
  match WordMap.find_opt m w with
  | None ->
     let state = UF.uref w in
     WordMap.add m w state;
     state
  | Some state -> state
           
exception Acceptance_mismatch of word * word
          
let equivalent_words (w1: word) (w2: word) (sigma: int) : bool =
  let m : state WordMap.t = WordMap.create 16 in
  let start1 = find_state m w1 in
  let start2 = find_state m w2 in
  UF.unite start1 start2;
  let rec loop (l: (word * word) list) : bool =
    match l with
    | [] -> true (* all done! *)
    | (w1, w2)::l' ->
       let rec inner (c: int) : (word * word) list=
         if c = sigma
         then []
         else begin
             debug (fun () -> Printf.printf "comparing %s and %s on %s\n"
                                (Word.show w1) (Word.show w2) (show_letter c));
             let push =
               match derivative w1 c, derivative w2 c with
               | None, None -> []
               | Some w1c, Some w2c ->
                  begin
                    debug (fun () -> Printf.printf "comparing %s and %s on %s\n"
                                       (Word.show w1) (Word.show w2) (show_letter c));

                    let st1 = find_state m w1c in
                    let st2 = find_state m w2c in
                    if accepting w1c <> accepting w2c
                    then raise (Acceptance_mismatch (w1c, w2c))
                    else if not (UF.equal st1 st2)
                    then begin
                        debug (fun () -> Printf.printf "uniting...\n");                          
                        UF.unite st1 st2;
                        [(w1c,w2c)]
                    end
                    else []
                  end
               | _, _ -> raise (Acceptance_mismatch (w1, w2))
             in
             push @ inner (c+1)
           end
       in
       try
         let app = inner 0 in
         debug (fun () -> Printf.printf "added %s\n"
                            (show_list (fun (w1,w2) ->
                                 "(" ^ Word.show w1 ^ ", " ^ Word.show w2 ^ ")")
                               app));
         loop (l' @ app)
       with Acceptance_mismatch (w1, w2) ->
         begin
           debug (fun () -> Printf.printf "%s and %s mismatch\n"
                              (Word.show w1) (Word.show w2));
           false
         end
  in
  loop [(w1, w2)]
