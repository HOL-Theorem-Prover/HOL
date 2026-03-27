(* Command-line utility to read and pretty-print theorems from HOL4 .dat files *)

structure DatPrinter = struct

open Portable
open RawTheory_dtype
open RawTheoryReader
open RawTermPP
open smpp

infix |>
fun x |> f = f x
infix >>

fun die s = (
  TextIO.output(TextIO.stdErr, "ERROR: " ^ s ^ "\n");
  TextIO.flushOut TextIO.stdErr;
  OS.Process.exit OS.Process.failure
)

(* Print a single theorem with decoded and pretty-printed term *)
fun pp_theorem tables (t : string raw_thm) =
  let
    val name = #name t
    val concl_str = #concl t
    val class_str = case #class t of
                      Axm => "Axm"
                    | Def => "Def"
                    | Thm => "Thm"
    val pp_concl = (RawTermPP.pp_term (RawTermPP.decode_term tables concl_str))
                   handle _ => add_string concl_str
  in
    block HOLPP.CONSISTENT 2 (
      add_string (name ^ " (" ^ class_str ^ "):") >>
      add_newline >>
      block HOLPP.INCONSISTENT 0 pp_concl
    )
  end

(* Print all theorems in a theory *)
fun pp_theory_file path =
  let
    val raw_theory = RawTheoryReader.load_raw_thydata {path = path}
      handle TheoryReader s => die ("Failed to read " ^ path ^ ": " ^ s)
           | e => die ("Unexpected error reading " ^ path ^ ": " ^ exnMessage e)

    val {name, exports, tables, ...} = raw_theory
    val {thms, ...} = exports
  in
    block HOLPP.CONSISTENT 0 (
      add_string ("Theory: " ^ name) >> add_newline >>
      add_string (Int.toString (List.length thms) ^ " theorems:") >>
      block HOLPP.CONSISTENT 2 (
        add_newline >>
        pr_list (pp_theorem tables) add_newline thms
      )
    )
  end

fun print_theory_file path =
  case smpp.lower (pp_theory_file path) () of
      SOME (pt, _, _) => (HOLPP.prettyPrint (print, 79) pt ; print "\n")
    | NONE => die "Failed to format output"

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
