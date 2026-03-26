(* Command-line utility to read and pretty-print theorems from HOL4 .dat files *)

structure DatPrinter = struct

open Portable
open RawTheory_dtype
open RawTheoryReader
open RawTermPP

infix |>
fun x |> f = f x

fun die s = (
  TextIO.output(TextIO.stdErr, "ERROR: " ^ s ^ "\n");
  TextIO.flushOut TextIO.stdErr;
  OS.Process.exit OS.Process.failure
)

fun println s = print (s ^ "\n")

(* Print a single theorem with decoded and pretty-printed term *)
fun print_theorem tables (t : string raw_thm) =
  let
    val name = #name t
    val concl_str = #concl t
    val class_str = case #class t of
                      Axm => "Axm"
                    | Def => "Def"
                    | Thm => "Thm"
    val pp_concl = (RawTermPP.pp_term (RawTermPP.decode_term tables concl_str))
                   handle _ => concl_str
  in
    println ("  " ^ name ^ " (" ^ class_str ^ "):");
    println ("    " ^ pp_concl)
  end

(* Print all theorems in a theory *)
fun print_theory_file path =
  let
    val raw_theory = RawTheoryReader.load_raw_thydata {path = path}
      handle TheoryReader s => die ("Failed to read " ^ path ^ ": " ^ s)
           | e => die ("Unexpected error reading " ^ path ^ ": " ^ exnMessage e)

    val {name, exports, tables, ...} = raw_theory
    val {thms, ...} = exports
  in
    println ("Theory: " ^ name);
    println (Int.toString (List.length thms) ^ " theorems:");
    List.app (print_theorem tables) thms
  end

(* Main entry point *)
fun main () =
    case CommandLine.arguments() of
      [] => (
        TextIO.output(TextIO.stdErr, "Usage: dat-printer <file.dat>\n");
        TextIO.flushOut TextIO.stdErr;
        OS.Process.exit OS.Process.failure
      )
    | [path] => print_theory_file path
    | _ => die "Too many arguments. Usage: dat-printer <file.dat>"

end
