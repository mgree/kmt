open Kat
open Automata
open Decide
open Common
   
let is_flag (s: string) : bool =
  String.length s > 2 && String.get s 0 = '-' && String.get s 1 = '-'

let driver_log_src = Logs.Src.create "kmt.driver"
                       ~doc:"logs KMT equivalence class driver"
module Log = (val Logs.src_log driver_log_src : Logs.LOG)
  
module Driver(T : THEORY) = struct
  module K = T.K
  module A = Automata(K)
  module D = Decide(T)

  let parse_normalize_and_show (s: string) : D.lanf =
    (* header *)
    let p = K.parse s in

    Log.app (fun m -> m "[%s parsed as %s]" s (K.Term.show p));
    
    (* normalization and lanf *)
    let (x, nf_time) = time (D.normalize_term 0) p in
    Log.info (fun m ->  m "nf = %s" (D.show_nf x));
    Log.app (fun m -> m "nf time: %fs" nf_time);

    let (xhat, lanf_time) = time D.locally_unambiguous_form x in
    Log.info (fun m -> m "lanf = %s" (D.show_nf xhat));
    Log.app (fun m -> m "lanf time: %fs" lanf_time);
    flush stdout;
    xhat

  let show_equivalence_classes (ps: D.lanf list) =
    let eqs = D.equivalence_classes_lanf ps in
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
                        (fun acc x -> D.show_nf x ^ Common.add_sep "; " acc) "" cls)))

  let run ss =
    let ps = List.map parse_normalize_and_show ss in
    if List.length ps > 1
    then show_equivalence_classes ps
end
