open HolKernel boolLib bossLib;
open stringSyntax sumSyntax;
open parse_jsonTheory;

(* TODO: This should be part of some standard library *)
val eval_rhs = rhs o concl o EVAL

(* TODO: This fits better in a "jsonSyntax.sml" *)
val string_to_json_tm =
  prim_mk_const {Thy = "parse_json", Name = "string_to_json"}

(* Hard-coded relative path to validation tests *)
val dir = "JSONTestSuite/test_parsing"

fun read_file path =
  let
    val stream = TextIO.openIn path
    val contents = TextIO.inputAll stream
    val _ = TextIO.closeIn stream
  in
    contents
  end

(* The JSONTestSuite naming convention for tests:
     y_ : should be accepted
     n_ : should be rejected
     i_ : either outcome is acceptable *)
fun process_directory dir =
  let
    val dir_stream = OS.FileSys.openDir dir
    val expected = ref 0
    val discrepancies = ref 0
    val errors = ref 0
    fun report msg counter =
      (TextIO.output (TextIO.stdOut, msg); counter := !counter + 1)
    fun check_file name =
      let
        val full_path = OS.Path.concat (dir, name)
      in
        if OS.FileSys.isDir full_path then ()
        else
          let
            val contents = read_file full_path
            val result_ok =
              is_inl $ eval_rhs $ mk_comb (string_to_json_tm, fromMLstring contents)
            val first_letter = String.sub (name, 0)
            val expect_ok = first_letter = #"y"
            val dont_care = first_letter = #"i"
          in
            if dont_care orelse (result_ok = expect_ok)
            then report ("Results as expected for file: " ^ name ^ "\n") expected
            else report ("Discrepancy found for file: " ^ name ^ "\n") discrepancies
          end
      end
      handle e =>
        report ("Error processing file: " ^ name ^ " (" ^ exnMessage e ^ ")\n") errors
    fun loop () =
      case OS.FileSys.readDir dir_stream of
          NONE => ()
        | SOME name => (check_file name; loop ())
  in
    loop ();
    OS.FileSys.closeDir dir_stream;
    TextIO.output (TextIO.stdOut,
      "\n=== Summary ===\n" ^
      "Expected:      " ^ Int.toString (!expected) ^ "\n" ^
      "Discrepancies: " ^ Int.toString (!discrepancies) ^ "\n" ^
      "Errors:        " ^ Int.toString (!errors) ^ "\n")
  end

fun main () = process_directory dir
