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
module D = Decide(Addition)

let main = 
(*  let a = K.parse "(x>1; inc(x,1) + y>1; inc(y,1))*" in 
  let b = K.parse "true" in 
  let eq = D.equivalent a b in *)
  let p = K.parse "x>1; inc(x,1) + y>1; inc(y,1) + inc(z,1)" in
  let x = D.normalize_term 0 p in
  let xhat = D.locally_unambiguous_form x in
  Printf.printf "x=%s\n\nx^ = %s\n" (D.show_nf x) (D.show_nf xhat);
  Printf.printf "p == p via normalization: %b\n" (D.equivalent p p);
  let q = K.parse "x>1;inc(x,1) + z>1;inc(z,1)" in
  let y = D.normalize_term 0 p in
  let yhat = D.locally_unambiguous_form y in
  Printf.printf "x=%s\n\nx^ = %s\n" (D.show_nf x) (D.show_nf yhat);
  Printf.printf "q == q via normalization: %b\n" (D.equivalent q q);
  Printf.printf "p == q via normalization: %b\n" (D.equivalent p q);
  let r = K.parse "x>1;inc(x,1) + z>1;inc(z,1)" in
  Printf.printf "q == r via normalization: %b\n" (D.equivalent q r)
  (*  Printf.printf "Equivalent (normalize): %b\n" (eq) *)

(*
let test = ref false
let stats = ref false
let in_file = ref None

let usage = "Usage: tkat [options]"
let params = [
    ("-in", Arg.String (fun s -> in_file := Some s), "Input file name (default stdin)");
    ("-stats", Arg.Unit (fun n -> stats := true), "Output performance statistics as csv to stdout");
    ("-test", Arg.Unit (fun _o -> test := true), "Runs unit tests" );
  ]

let _ =
  try begin
    Arg.parse params (fun x -> raise (Arg.Bad ("Bad argument : " ^ x))) usage;
  end
  with
    | Arg.Bad msg -> Printf.printf "%s" msg
    | Arg.Help msg -> Printf.printf "%s" msg
*)
