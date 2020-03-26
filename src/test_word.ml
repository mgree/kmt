open Word
open Alcotest

let same_words (w1: word) (w2: word) : bool =
  let sigma = max (num_letters w1) (num_letters w2) in
  equivalent_words w1 w2 sigma
   
(* TODO better pretty printing *)
let equiv : word testable =
  let pp = Fmt.of_to_string Word.show in
  testable pp same_words

let check_equivalent = check equiv "equivalent"
  
let small_words = [
    emp
  ; eps
  ; ltr 0
  ; ltr 1
  ; ltr 2
  ]

let rec concat_map (f: 'a -> 'b list) (l: 'a list) : 'b list =
  match l with
  | [] -> []
  | (a::l') -> f a @ concat_map f l'
          
let cartesian_product (l1: 'a list) (l2: 'b list) : ('a * 'b) list =
  concat_map (fun a -> List.map (fun b -> (a,b)) l2) l1

let uncurry (f: 'a -> 'b -> 'c) ((a, b): 'a * 'b) : 'c = f a b
  
let alts (ws: word list) = cartesian_product ws ws |> List.map (uncurry alt)
let cats (ws: word list) = cartesian_product ws ws |> List.map (uncurry cat)
let strs (ws: word list) = ws |> List.map str 

let rec transform (l: 'a list) (xforms: ('a list -> 'a list) list) (lvls: int) : 'a list =
  if lvls <= 0
  then l
  else transform (l @ concat_map (fun xform -> xform l) xforms) xforms (lvls - 1)

let star_free_words : word list =
  transform small_words [alts; cats] 1 (* TODO MMG 2020-03-26 change to 2 *)
  
let words : word list =
  transform (transform small_words [alts; cats; strs] 1) [strs] 1

let rec unroll_star_r (w: word) : word =
  match w.node with
  | Str w_inner -> alt eps (cat w_inner w)
  | Emp | Eps | Ltr _ -> w
  | Alt (w1, w2) -> alt (unroll_star_r w1) (unroll_star_r w2)
  | Cat (w1, w2) -> cat (unroll_star_r w1) (unroll_star_r w2)

let rec unroll_star_l (w: word) : word =
  match w.node with
  | Str w_inner -> alt (cat w w_inner) eps
  | Emp | Eps | Ltr _ -> w
  | Alt (w1, w2) -> alt (unroll_star_r w1) (unroll_star_r w2)
  | Cat (w1, w2) -> cat (unroll_star_r w1) (unroll_star_r w2)

let main () =
  run "word equivalence of regular expressions" [
      "reflexivity",
      words |>
        List.map (fun w ->
            test_case ("reflexivity (" ^ Word.show w ^ ")") `Quick
              (fun () -> check_equivalent w w))
    ; "symmetry",
      cartesian_product words words |>
        List.map (fun (w1, w2) ->
            test_case ("symmetry (" ^ Word.show w1 ^ " and " ^ Word.show w2 ^ ")") `Quick
              (fun () -> check bool "same answer" (same_words w1 w2) (same_words w2 w1)))
    ; "star unrolling (w* = 1 + ww*)",
      star_free_words |> strs |>
        List.map (fun w ->
            test_case ("star unrolling (" ^ Word.show w ^ ")") `Quick
              (fun () -> check_equivalent w (unroll_star_r w)))
    ; "star unrolling (w* = w*w + 1)",
      star_free_words |> strs |>
        List.map (fun w ->
            test_case ("star unrolling (" ^ Word.show w ^ ")") `Quick
              (fun () -> check_equivalent w (unroll_star_l w)))
    ; let w = str (alt (ltr 0) (alt emp (ltr 1))) in
      "debugging slowness", [
          test_case "reflexivity (pi_0 + false + pi_1 )*" `Quick
            (fun () -> check_equivalent w w)
        ; test_case "reflexivity (pi_0 + false + pi_1 )**" `Quick
            (fun () -> check_equivalent (str w) (str w))
        ; test_case "star unrolling (w* = 1 + ww*)" `Quick
            (fun () -> check_equivalent w (unroll_star_r w))
        ; test_case "star unrolling (w* = w*w + 1)" `Slow
            (fun () -> check_equivalent w (unroll_star_l w))
      ]
    ]
;;

main ()
