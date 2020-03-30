open Common
open Word
open Alcotest
   
(* TODO better pretty printing *)
let equiv : word testable =
  let pp = Fmt.of_to_string Word.show in
  testable pp same_words

let check_equivalent = check equiv "equivalent"

let check_inequivalent = check (neg equiv) "inequivalent"

let small_words = [
    emp
  ; eps
  ; ltr 0
  ; ltr 1
  ; ltr 2
  ]

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

let debug_mode () =
  Logs.Src.set_level word_log_src (Some Logs.Debug);
  Logs.set_reporter (Logs_fmt.reporter ())
                  
let main () =
  debug_mode ();
  run "word equivalence of regular expressions" [
      "reflexivity",
      [test_case ("reflexivity (" ^ string_of_int (List.length words) ^ " cases)") `Quick
         (fun () -> words |> List.iter (fun w -> check_equivalent w w))]
    ; "symmetry",
      begin
        let pairs = unique_pairs words in
        [test_case ("w1 = w2 <-> w2 = w1 (" ^ string_of_int (List.length pairs) ^ " cases)") `Quick
           (fun () -> pairs
                      |> List.iter (fun (w1, w2) ->
                             check bool ("same answer for " ^ Word.show w1 ^ " and " ^ Word.show w2)
                               (same_words w1 w2) (same_words w2 w1)))]
      end
    ; "star unrolling (w* = 1 + ww*)",
      begin
        let ws = star_free_words |> strs in
        [test_case ("w = unroll w (" ^ string_of_int (List.length ws) ^ " cases)") `Quick
           (fun () -> ws |> List.iter (fun w -> check_equivalent w (unroll_star_r w)))]
      end
    ; "star unrolling (w* = w*w + 1)",
      begin
        let ws = star_free_words |> strs in
        [test_case ("w = unroll w (" ^ string_of_int (List.length ws) ^ " cases)") `Quick
           (fun () -> ws |> List.iter (fun w -> check_equivalent w (unroll_star_l w)))]
      end
    ; "inequivalences",
      [ test_case "true != false" `Quick (fun () -> check_inequivalent eps emp)
      ; test_case "pi_0 != pi_1" `Quick (fun () -> check_inequivalent (ltr 0) (ltr 1))
      ; test_case "pi_0 != pi_0 + pi_1" `Quick
          (fun () -> check_inequivalent (ltr 0) (alt (ltr 0) (ltr 1)))
      ; test_case "pi_0* != pi_0*" `Quick
          (fun () -> check_inequivalent (ltr 0) (str (ltr 1)))
      ; begin
          let ws = star_free_words |> strs in
          test_case ("w* != false (" ^ string_of_int (List.length ws) ^ " cases)") `Quick
            (fun () -> ws |> List.iter (fun w -> check_inequivalent w emp))
        end
      ]
    ; let w = str (alt (ltr 0) (alt emp (ltr 1))) in
      "debugging slowness (w = (pi_0 + false + pi_1)*)", [
          test_case "reflexivity on w" `Quick
            (fun () -> check_equivalent w w)
        ; test_case "reflexivity on w*" `Quick
            (fun () -> check_equivalent (str w) (str w))
        ; test_case "right unrolling (w* = 1 + ww*)" `Quick
            (fun () -> check_equivalent w (unroll_star_r w))
        ; test_case "left unrolling (w* = w*w + 1)" `Slow
            (fun () -> check_equivalent w (unroll_star_l w))
      ]
    ]
;;

main ()
