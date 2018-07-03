open Kat
open Addition
open Network
open Automata
open Complete
open Decide
open Product
open Boolean

module K = Addition.K
module A = Automata(K)

let main = 
  let a = K.parse "(inc(x,1);x>1)*" in 
  let b = K.parse "true + x>0;inc(x,1);inc(x,1)*" in 
  let auto1 = A.of_term a in 
  let auto2 = A.of_term b in 
  let eq = A.equivalent auto1 auto2 in
  Printf.printf "Equivalent (normalize): %b\n" (eq)

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