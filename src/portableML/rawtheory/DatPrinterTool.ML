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
fun pp_theorem tables unquals (t : string raw_thm) =
  let
    val name = #name t
    val concl_str = #concl t
    val class_str = case #class t of
                      Axm => "Axm"
                    | Def => "Def"
                    | Thm => "Thm"
    val pp_concl = (RawTermPP.pp_term unquals (RawTermPP.decode_term tables concl_str))
                   handle _ => add_string concl_str
  in
    block HOLPP.CONSISTENT 2 (
      add_string (name ^ " (" ^ class_str ^ "):") >>
      add_newline >>
      block HOLPP.INCONSISTENT 0 pp_concl
    )
  end

(* Print all theorems in a theory *)
fun pp_theory_file unquals path =
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
        pr_list (pp_theorem tables unquals) add_newline thms
      )
    )
  end

fun print_theory_file unquals path =
  case smpp.lower (pp_theory_file unquals path) () of
      SOME (pt, _, _) => (HOLPP.prettyPrint (print, 79) pt ; print "\n")
    | NONE => die "Failed to format output"

datatype conf_record = CR of { unquals : string list, help : bool }
val init_conf = CR { unquals = ["bool", "min", "num", "sum", "pair", "option"], help = false }

fun add_unqual th (CR {unquals, help}) = CR {unquals = th :: unquals, help = help}
fun rm_unqual th (CR {unquals, help}) = CR {unquals = List.filter (fn t => t <> th) unquals, help = help}
fun clear_unquals () (CR {unquals, help}) = CR {unquals = [], help = help}
fun set_help () (CR {unquals, help= _}) = CR {unquals = unquals, help = true}

val cline_options = [
  {short = "u", long = ["unqualify"], desc = GetOpt.ReqArg (add_unqual, "thy"), help = "Add a theory to the unqualified list"},
  {short = "q", long = ["qualify"], desc = GetOpt.ReqArg (rm_unqual, "thy"), help = "Remove a theory from the unqualified list"},
  {short = "c", long = ["clear-unquals"], desc = GetOpt.NoArg clear_unquals, help = "Clear the default unqualified list"},
  {short = "h", long = ["help"], desc = GetOpt.NoArg set_help, help = "Show this message"}
]

(* Main entry point *)
fun main () =
  let
    val uheader = "Usage: dat-printer [options] <file.dat>"
    val uinfo = GetOpt.usageInfo {header = uheader, options = cline_options}
    val (cline_upds, files) =
        GetOpt.getOpt {argOrder = GetOpt.Permute,
                       options = cline_options,
                       errFn = fn s => die (s ^ "\n" ^ uinfo)}
                      (CommandLine.arguments())
    val CR {unquals, help} = List.foldl (fn (f, acc) => f acc) init_conf cline_upds
  in
    if help then (
        TextIO.output(TextIO.stdOut, uinfo);
        OS.Process.exit OS.Process.success
    ) else
    case files of
      [] => (
        TextIO.output(TextIO.stdErr, uinfo);
        OS.Process.exit OS.Process.failure
      )
    | [path] => print_theory_file unquals path
    | _ => die ("Too many arguments.\n" ^ uinfo)
  end

end
