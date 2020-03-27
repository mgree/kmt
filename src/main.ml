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

let modes =
  [ "--boolean", DBoolean.main (* default *)
  ; "--incnat", DIncNat.main
  ; "--addition", DIncNat.main
  ; "--network", DNetwork.main
  ; "--product", DProduct.main
  ]

let selected_mode =
  let rec loop i =
    if i >= Array.length Sys.argv
    then snd (List.hd modes) (* default *)
    else if is_flag Sys.argv.(i)
    then
      begin
        match List.find_opt (fun (mode,_main) -> BatString.starts_with mode Sys.argv.(i))
                modes with
        | None -> loop (i+1)
        | Some (_mode, main) -> main
      end
    else loop (i+1)
  in
  loop 1

let setup_log style_renderer level : unit =
  Fmt_tty.setup_std_outputs ?style_renderer ();
  Logs.set_level level;
  Logs.set_reporter (Logs_fmt.reporter ());
  ()

let main () =
  setup_log (Some `Ansi_tty)
    (Some (if Common.debug_enabled
           then Logs.Debug
           else if Common.quiet_enabled
           then Logs.Error
           else Logs.Info));
  if Array.length Sys.argv < 2
  then begin
      Log.err (fun m -> m "Usage: %s [--debug] [--quiet] [--MODE] [KAT term] ...\n\tMODE = boolean (DEFAULT) | incnat | addition | network | product (of boolean/incnat)\n"
                          Sys.executable_name);
      exit 2
    end
  else selected_mode Sys.argv
;;

main ()
