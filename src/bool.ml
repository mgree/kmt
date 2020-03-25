open Kat
open Automata
open Complete
open Decide
open Boolean

module T = ANSITerminal
   
module K = Boolean.K
module A = Automata(K)
module D = Decide(Boolean)          

let parse_normalize_and_show (s: string) : D.lanf =
  let p = K.parse s in
  T.printf [] "["; T.printf [T.Bold] "%s" s; T.printf [] " parsed as "; T.printf [T.Bold] "%s" (K.Term.show p); T.printf [] "]\n%!";
  let x = D.normalize_term 0 p in
  T.printf [] "  nf = "; T.printf [T.yellow] "%s\n%!" (D.show_nf x);
  let xhat = D.locally_unambiguous_form x in
  T.printf [] "  lanf = "; T.printf [T.green] "%s\n%!"(D.show_nf xhat);
  xhat
  
let main =
  if Array.length Sys.argv < 2
  then begin
      T.printf [] "Usage: %s [--debug] [boolean KAT term] ..." Sys.executable_name;
      exit 2
    end
  else
    let terms = Sys.argv |> Array.to_list |> List.tl |> List.filter (fun s -> s <> "--debug") in
    let ps = List.map parse_normalize_and_show terms in
    if List.length ps > 1
    then begin
        let eqs = D.equivalence_classes_lanf ps in
        let num_eqs = List.length eqs in
        T.printf [] "\n["; T.printf [T.Bold; T.red] "%d" num_eqs; T.printf [T.Bold] " equivalence class%s" (if num_eqs > 1 then "es" else ""); T.printf [] "]\n";
        eqs |> List.iteri
                 (fun i cls ->
                   T.printf [T.Bold] "%d: " (i+1);
                   List.fold_left (fun acc x -> D.show_nf x ^ Common.add_sep "; " acc) "" cls |> T.printf [] "[%s]\n" 
                 )
      end
