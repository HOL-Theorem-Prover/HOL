open testutils Holmake_types

(* Holmakefile `include' directive parser tests.  Each sub-test
   uses ReadHMF.read on a sample file and asserts properties of
   the returned env / behaviour. *)

fun read fname = ReadHMF.read fname (base_environment())

(* Look up a variable in env; returns SOME expanded value, or NONE
   when the variable is unset (which Holmake's lookup represents
   by an empty quotation that substitutes to ""). *)
fun lookup_val env name =
    let val s = perform_substitution internal_functions.default_diags
                                     env [VREF name]
    in if s = "" then NONE else SOME s
    end

fun has_var env name = isSome (lookup_val env name)

fun result_str (env, _, _, _) =
    "env keys: " ^ String.concatWith ", " (env_keys env)

(* ----- 1. simple: parent includes one child file ----- *)
fun check_simple (env, _, _, _) =
    has_var env "FOO" andalso
    has_var env "BAR" andalso
    has_var env "CHILD_VAR" andalso
    lookup_val env "CHILD_VAR" = SOME "from_child"

val _ = tprint "include: child file's vars appear in env"
val _ = require_msg (check_result check_simple) result_str
                    read "simple_parent"

(* ----- 2. nested: A -> B -> C, all vars present ----- *)
fun check_nested (env, _, _, _) =
    has_var env "A_VAR" andalso has_var env "A_AFTER" andalso
    has_var env "B_VAR" andalso has_var env "B_AFTER" andalso
    has_var env "C_VAR" andalso
    lookup_val env "C_VAR" = SOME "deeply_nested"

val _ = tprint "include: vars from a transitively-included file present"
val _ = require_msg (check_result check_nested) result_str
                    read "nested_a"

(* ----- 3. multi-file: include foo bar ----- *)
fun check_multi (env, _, _, _) =
    has_var env "ONE" andalso has_var env "TWO" andalso
    has_var env "PARENT_VAR"

val _ = tprint "include: multiple files on one directive"
val _ = require_msg (check_result check_multi) result_str
                    read "multi_parent"

(* ----- 4. variable expansion in include path ----- *)
fun check_var_path (env, _, _, _) =
    has_var env "SUBDIR" andalso
    has_var env "VAR_FROM_SUBDIR" andalso
    lookup_val env "VAR_FROM_SUBDIR" = SOME "found"

val _ = tprint "include: $(VAR) in path expanded against env-so-far"
val _ = require_msg (check_result check_var_path) result_str
                    read "var_parent"

(* ----- 5. cycle detection ----- *)
val _ = tprint "include: cycle A -> B -> A errors"
val _ = shouldfail
          {testfn = read,
           printresult = result_str,
           printarg = fn s => s,
           checkexn = fn Fail s => String.isSubstring "cycle" s
                       | _ => false}
          "cycle_a"

(* ----- 6. missing file: mandatory `include' raises ----- *)
val _ = tprint "include: missing mandatory file errors"
val _ = shouldfail
          {testfn = read,
           printresult = result_str,
           printarg = fn s => s,
           checkexn = fn Fail s => String.isSubstring "can't open include" s
                       | _ => false}
          "missing_parent"

(* ----- 7. missing optional: -include / sinclude silently skip ----- *)
fun check_optional (env, _, _, _) =
    has_var env "BEFORE" andalso has_var env "AFTER"

val _ = tprint "-include / sinclude: missing files silently skipped"
val _ = require_msg (check_result check_optional) result_str
                    read "optional_parent"

(* ----- 8. include wrapped in a false ifdef: balanced ok ----- *)
fun check_condok (env, _, _, _) = has_var env "AFTER"

val _ = tprint "include: ok when wrapped in (false) ifdef"
val _ = require_msg (check_result check_condok) result_str
                    read "condok_parent"

(* ----- 9. conditional imbalance in included file errors ----- *)
val _ = tprint "include: child with unterminated ifdef errors"
val _ = shouldfail
          {testfn = read,
           printresult = result_str,
           printarg = fn s => s,
           checkexn =
             fn Fail s => String.isSubstring "unterminated" s andalso
                          String.isSubstring "condbad_child" s
              | _ => false}
          "condbad_parent"
