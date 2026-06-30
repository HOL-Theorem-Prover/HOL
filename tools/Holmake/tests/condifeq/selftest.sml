open testutils Holmake_types

(* ifeq / ifneq paren-form: the comma that separates the two
   arguments must be the first one at top-level (outside any nested
   $(...) or ${...}).  A naive "first literal comma" split would
   chop apart make function calls whose arguments themselves
   contain commas (patsubst, call, if, ...). *)

fun read fname = ReadHMF.read fname (base_environment())

fun lookup_val env name =
    let val s = perform_substitution internal_functions.default_diags
                                     env [VREF name]
    in if s = "" then NONE else SOME s
    end

fun result_of (env, _, _, _) = lookup_val env "RESULT"

fun expect want (env, _, _, _) = lookup_val env "RESULT" = SOME want

fun result_str r =
    case result_of r of
      NONE => "RESULT unset"
    | SOME v => "RESULT = " ^ v

(* ----- 1. inner commas inside $(patsubst ...) are not separators ----- *)
val _ = tprint "ifeq: $(patsubst ...) with inner commas in arg1"
val _ = require_msg (check_result (expect "matched")) result_str
                    read "nestedfn"

(* ----- 2. ifneq counterpart, with arg mismatch -> else taken ----- *)
val _ = tprint "ifneq: $(patsubst ...) inner commas, else branch"
val _ = require_msg (check_result (expect "neqfalse")) result_str
                    read "nestedfn_neq"

(* ----- 3. ${...} braces nest the same way as $(...) ----- *)
val _ = tprint "ifeq: ${patsubst ...} braces nest like parens"
val _ = require_msg (check_result (expect "matched")) result_str
                    read "braces"

(* ----- 4. $(if cond,then,else) -- multiple inner commas ----- *)
val _ = tprint "ifeq: $(if ...) with two inner commas in arg1"
val _ = require_msg (check_result (expect "matched")) result_str
                    read "calln"

(* ----- 5. empty RHS still parses (off-by-one regression guard) ----- *)
val _ = tprint "ifeq: empty second argument parses"
val _ = require_msg (check_result (expect "matched")) result_str
                    read "emptylhs"

(* ----- 6. simple form unchanged ----- *)
val _ = tprint "ifeq: plain (a,a) still works"
val _ = require_msg (check_result (expect "matched")) result_str
                    read "baresplit"

(* ----- 7. missing separator comma still raises ----- *)
val _ = tprint "ifeq: no comma in args still errors"
val _ = shouldfail
          {testfn = read,
           printresult = result_str,
           printarg = fn s => s,
           checkexn =
             fn Fail s => String.isSubstring "separated by commas" s
              | _ => false}
          "missingcomma"
