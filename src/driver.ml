open Kat
open Automata
open Decide
open Common
   
module P = ANSITerminal

let is_flag (s: string) : bool =
  String.length s > 2 && String.get s 0 = '-' && String.get s 1 = '-'

module Driver(T : THEORY) = struct
  module K = T.K
  module A = Automata(K)
  module D = Decide(T)

  let parse_normalize_and_show (s: string) : D.lanf =
    (* header *)
    let p = K.parse s in
    P.printf [] "[";
    P.printf [P.Bold] "%s" s;
    P.printf [] " parsed as ";
    P.printf [P.Bold] "%s" (K.Term.show p);
    P.printf [] "]\n%!";
    
    (* normalization and lanf *)
    let (x, nf_time) = time (D.normalize_term 0) p in
    loud (fun () ->  P.printf [] "  nf = "; P.printf [P.yellow] "%s\n%!" (D.show_nf x));
    P.printf [P.cyan] "  nf time: %fs\n%!" nf_time;
    let (xhat, lanf_time) = time D.locally_unambiguous_form x in
    loud (fun () -> P.printf [] "  lanf = "; P.printf [P.green] "%s\n%!"(D.show_nf xhat));
    P.printf [P.cyan] "  lanf time: %fs\n%!" lanf_time;
    flush stdout;
    xhat

  let show_equivalence_classes (ps: D.lanf list) =
    let eqs = D.equivalence_classes_lanf ps in
    let num_eqs = List.length eqs in
    
    (* header *)
    P.printf [] "\n[";
    P.printf [P.Bold; P.red] "%d" num_eqs;
    P.printf [P.Bold] " equivalence class%s" (if num_eqs > 1 then "es" else "");
    P.printf [] "]\n";

    (* classes *)
    loud (fun () ->
        eqs |> List.iteri
                 (fun i cls ->
                   P.printf [P.Bold] "%d: " (i+1);
                   List.fold_left (fun acc x -> D.show_nf x ^ Common.add_sep "; " acc) "" cls
                   |> P.printf [] "[%s]\n"))

  let main argv =
    if Array.length Sys.argv < 2
    then begin
        P.printf [] "Usage: %s [--debug] [--quiet] [--MODE] [%s KAT term] ...\n\tMODE = boolean (DEFAULT) | incnat | addition | network | product (of boolean/incnat)\n"
          Sys.executable_name (T.name ());
        exit 2
      end
    else
      let ps =
        Sys.argv
        |> Array.to_list
        |> List.tl
        |> List.filter (fun s -> not (is_flag s))
        |> List.map parse_normalize_and_show
      in
      if List.length ps > 1
      then show_equivalence_classes ps
end
