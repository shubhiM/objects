open Compile
open Runner
open Printf
open Lexing
open Exprs
open Errors
open Phases
open Inference

let show_trace = ref false
let filename_set = ref false
let filename : string ref = ref ""
;;
Printexc.record_backtrace true
;;     
let () =
  let speclist = [
      ("-t", Arg.Set show_trace, "Display the trace of compilation");
      ("-no-tc", Arg.Set skip_typechecking, "Skip static type checking");
      ("-d", Arg.Set show_debug_print, "Enable debug printing")
    ] in
  Arg.parse speclist (fun name ->
      if !filename_set then
        raise (Arg.Bad "Cannot compile more than one file name")
      else
        (filename_set := true;
         filename := name)
    ) "Taipan compiler options:";
  
  match compile_file_to_string (!filename) (!filename) with
  | Error (errs, trace) ->
     eprintf "Errors:\n";
     (if !show_trace then
        eprintf "%s\n" (ExtString.String.join "\n=================\n" (print_trace trace))
      else ());
     eprintf "%s\n" (ExtString.String.join "\n" (print_errors errs))
  | Ok (program, trace) ->
     if !show_trace then
       printf "%s\n" (ExtString.String.join "\n=================\n" (print_trace trace))
     else
       printf "%s\n" program;;

