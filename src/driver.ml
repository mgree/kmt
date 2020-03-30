open Kat
open Automata
open Decide
open Common
   
let is_flag (s: string) : bool =
  String.length s > 2 && String.get s 0 = '-' && String.get s 1 = '-'

let driver_log_src = Logs.Src.create "kmt.driver"
                       ~doc:"logs KMT equivalence class driver"
module Log = (val Logs.src_log driver_log_src : Logs.LOG)

type decision_procedure = Normalization | Automata
           
module Driver(T : THEORY) = struct
  module K = T.K
  module A = Automata(K)
  module D = Decide(T)

  let parse_and_show (s: string) : K.Term.t =
    let p = K.parse s in

    Log.app (fun m -> m "[%s parsed as %s]" s (K.Term.show p));
    p
           
  let parse_normalize_and_show (s: string) : D.lunf =
    let p = parse_and_show s in
    
    (* normalization and lunf *)
    let (x, nf_time) = time (D.normalize_term 0) p in
    Log.info (fun m ->  m "nf = %s" (D.show_nf x));
    Log.app (fun m -> m "nf time: %fs" nf_time);

    let (xhat, lunf_time) = time D.locally_unambiguous_form x in
    Log.info (fun m -> m "lunf = %s" (D.show_nf xhat));
    Log.app (fun m -> m "lunf time: %fs" lunf_time);
    flush stdout;
    xhat

  let parse_automatize_and_show (s: string) : A.t =
    let p = parse_and_show s in
    
    (* conversion to automaton *)
    let (auto, auto_time) = time A.of_term p in
    Log.info (fun m ->  m "%s" (A.to_string auto));
    Log.app (fun m -> m "time: %fs" auto_time);
    auto
    
  let show_equivalence_classes (eq_dec: 'a -> 'a -> bool) (show: 'a -> string) (ps: 'a list) =
    let eqs = equivalence_classes eq_dec ps in
    let num_eqs = List.length eqs in
    
    (* header *)
    Log.app (fun m ->
        m "[%d equivalence class%s]" num_eqs (if num_eqs > 1 then "es" else ""));

    (* classes *)
    eqs |> List.iteri
             (fun i cls ->
               Log.info (fun m ->
                   m "%d: %s" (i+1)
                     (List.fold_left
                        (fun acc x -> show x ^ Common.add_sep "; " acc) "" cls)))
    
  let run dec ss =
    let go parse eq_dec show ss =
      let xs = List.map parse ss in
      if List.length xs > 1
      then show_equivalence_classes eq_dec show xs
    in
    match dec with
    | Normalization -> go parse_normalize_and_show D.equivalent_lunf D.show_nf ss
    | Automata -> go parse_automatize_and_show A.equivalent A.to_string ss
       
end
