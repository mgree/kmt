open Kat
open Addition
open Network
open Automata
open Complete
open Decide
open Product
open Boolean

module Prod = Product(Addition)(Boolean)
module KP = Prod.K
module C = CompleteTheory(Prod)
module D = Decide(C)

let main = 
  let a = D.K.parse "y<0; a=T; inc(y,1); (true + b=T; inc(y,1)); (true + c=T; inc(y,1)); y>0" in 
  let b = D.K.parse "a=T; b=T; c=T; inc(y,1); inc(y,1); inc(y,1)" in 
  let eq = D.equivalent a b in
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