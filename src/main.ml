open Kat
open Addition
open Network
open Product
open Boolean
open Incnat

open Driver

module DBoolean = Driver(Boolean)
module DIncNat = Driver(IncNat)
module DAddition = Driver(Addition)
module DNetwork = Driver(Network)
module DProduct = Driver(Product(Boolean)(IncNat))

open Cmdliner

let decision_procedure =
  let normalization =
    let doc = "select normalization/rewriting-based equivalence decision procedure (default)" in
    Normalization, Arg.info ["norm"; "rewrite"; "normalization"] ~doc
  in
  let automata =
    let doc = "select automata-based equivalence decision procedure" in
    Automata, Arg.info ["auto"; "automata"] ~doc
  in
  Arg.(last & vflag_all [Normalization] [normalization; automata])
   
let mode =
  let boolean =
    let doc = "KMT THEORY of boolean (default)\npredicates: x=F, x=T; actions: set(x,T), set(x,F)" in
    DBoolean.run, Arg.info ["boolean"] ~doc
  in
  let incnat =
    let doc = "KMT THEORY of monotonic naturals\npredicates: x>n; actions: inc(x), set(x,n)" in
    DIncNat.run, Arg.info ["incnat"] ~doc
  in
  let addition =
    let doc = "KMT THEORY of naturals with more predicates\npredicates: x>n, x<n; actions: inc(x), set(x,n)" in
    DAddition.run, Arg.info ["addition"] ~doc
  in
  let network =
    let doc = "KMT THEORY of tracing NetKAT\npredicates: {src,dst,pt,sw}=n; actions: {src,dst,pt,sw}<-n" in
    DNetwork.run, Arg.info ["network"] ~doc
  in
  let product =
    let doc = "KMT product theory of booleans and monotonic naturals" in
    DProduct.run, Arg.info ["product"] ~doc
  in
  Arg.(last & vflag_all [DBoolean.run]
                [boolean; incnat; addition; network; product])

let args = Arg.(non_empty & pos_all string [] & info [] ~docv:"KAT term")

let setup_log style_renderer level : unit =
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  Logs.set_reporter (Logs_fmt.reporter ());
  ()
         
let setup_log =
  Term.(const setup_log $ Fmt_cli.style_renderer () $ Logs_cli.level ())

let run dec mode args () = mode dec args
  
let cmd =
  let doc = "compute equivalence classes for various KMT theories" in
  Term.(const run $ decision_procedure $ mode $ args $ setup_log),
  Term.info "kmt" ~version:"v0.1" ~exits:Term.default_exits ~doc
  
let main () = Term.(exit @@ eval cmd)

;;

main ()
