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
   
let mode =
  let boolean =
    let doc = "default mode; predicates: x=F, x=T; actions: set(x,T), set(x,F)" in
    DBoolean.run, Arg.info ["boolean"] ~doc
  in
  let incnat =
    let doc = "predicates: x>n; actions: inc(x), set(x,n)" in
    DIncNat.run, Arg.info ["incnat"] ~doc
  in
  let addition =
    let doc = "predicates: x>n, x<n; actions: inc(x), set(x,n)" in
    DAddition.run, Arg.info ["addition"] ~doc
  in
  let network =
    let doc = "predicates: {src,dst,pt,sw}=n; actions: {src,dst,pt,sw}<-n" in
    DNetwork.run, Arg.info ["network"] ~doc
  in
  let product =
    let doc = "product of boolean and incnat" in
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

let run mode args () = mode args
  
let cmd =
  let doc = "compute equivalence classes for various KMT theories" in
  Term.(const run $ mode $ args $ setup_log),
  Term.info "kmt" ~version:"v0.1" ~exits:Term.default_exits ~doc
  
let main () = Term.(exit @@ eval cmd)

;;

main ()
