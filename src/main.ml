open Kat
open Addition
open Network
open Automata
open Decide

(* module Net = Complete.CompleteTheory(Network)
module D = Decide(Net) *)
module K = Addition.K
module A = Automata(K)

let main = 
  (* let x = K.parse "(inc(x,1) + x>10)*" in *)
  (* let x = K.parse "true" in
  let y = K.parse "true + sw=2;sw<-2" in *)
  let x = K.parse "(x>1) + (y>1)" in
  let y = K.parse "(y>1) + (x>1)" in
  (* Printf.printf "Term x:       %s\n" (K.Term.show x);
  Printf.printf "Term y:       %s\n" (K.Term.show y);
  Printf.printf "Normalized x: %s\n" (K.Term.show (D.normalize x));
  Printf.printf "Normalized y: %s\n" (K.Term.show (D.normalize y));
  Printf.printf "Equvialent: %b\n" (D.equivalent x y); *)
  let a1 = A.of_term x in 
  let a2 = A.of_term y in
  Printf.printf "Equivalent (tracing): %b\n" (A.equivalent a1 a2);


(*
let test = ref false
let stats = ref false
let in_file = ref None

let usage = "Usage: tkat [options]"
let params = [
    ("-in", Arg.String (fun s -> in_file := Some s), "Input file name (default stdin)");
    ("-stats", Arg.Unit (fun n -> stats := true), "Output performance statistics as csv to stdout");
    ("-test", Arg.Unit (fun _ -> test := true), "Runs unit tests" );
  ]

let _ =
  try begin
    Arg.parse params (fun x -> raise (Arg.Bad ("Bad argument : " ^ x))) usage;
  end
  with
    | Arg.Bad msg -> Printf.printf "%s" msg
    | Arg.Help msg -> Printf.printf "%s" msg
*)