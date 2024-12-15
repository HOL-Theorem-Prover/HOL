open HolKernel Parse boolLib
open testutils TotalDefn
val _ = Feedback.emit_MESG := false

fun badpp x = HOLPP.add_string "<Can't print this>"

fun EVAL t = computeLib.CBV_CONV computeLib.the_compset t
val _ = tprint "Testing mutually recursive function definition"

val f_def = require (check_result (K true)) Define`
  (f x = if x = 0 then T else ~g(x - 1)) /\
  (g x = if x = 0 then F else ~f(x - 1))
`

val _ = tprint "Testing definition over literals"

val h_def = Define`
  (h 0 = T) /\ (h 1 = F)
`;

val _ = let
  val cs = strip_conj (concl h_def)
  val _ = if length cs = 2 then () else die "FAILED!"
  val _ = if List.all (is_const o rhs) cs then () else die "FAILED!"
in
  OK()
end

val _ = tprint "Testing form of derived induction principle"
val fact_def = Define`fact n = if n < 2 then 1 else n * fact(n - 1)`;

val desired_ind =
  ``!P. (!n. (~(n < 2) ==> P (n - 1)) ==> P n) ==> !v. P v``

val _ = if aconv desired_ind (concl (theorem "fact_ind")) then OK()
        else die "FAILED!\n"

val _ = tprint "Define schema(1)"
val _ = require (check_result (K true)) (quietly DefineSchema)
                `(fs 0 y = z + y) /\ (fs x y = x)`;
val _ = tprint "Define schema(2)"
val _ = require (check_result (K true)) (quietly DefineSchema)
                `(gs 0 y = x + y) /\ (gs x y = x)`;

val _ = tprint "Testing 0-arg recursive function with lambda"

val f1_def = require (check_result (K true)) (quietly Define)`
  f1 = \x. case x of 0 => 0n | SUC n => f1 n
`

val _ = tprint "Testing 1-arg recursive function with lambda"

val f1_def = require (check_result (K true)) (quietly Define)`
  f2 (y : 'a) = \x. case x of 0 => 0n | SUC n => f2 y n
`;

val _ = tprint "Testing 2-arg recursive function with lambda"

val f1_def = require (check_result (K true)) (quietly Define)`
  f3 (y : 'a) (z : 'a) = \x. case x of 0 => 0n | SUC n => f3 y z n
`;

val _ = tprint "Testing 2-arg mutual recursive function"

val f4_def = require (check_result (K true)) (quietly Define)`
  f4 0 x = (0, x) /\
  f4 (SUC n) x = f5 n (x, x) /\
  f5 0 (x, y) = (0, y) /\
  f5 (SUC n) (x, y) = f4 n x
`;

fun tdefoutput_pp(th,thopt) =
    "(" ^ thm_to_string th ^ ", " ^
    (case thopt of NONE => "NONE"
                 | SOME th' => "SOME " ^ thm_to_string th') ^ ")"
fun quietDefn f x =
    Lib.with_flag (Globals.interactive, false) f x
val _  = shouldfail { checkexn = is_struct_HOL_ERR "TotalDefn",
                      printarg = K "tDefine: no schematic defs when \
                                   \termination tac is supplied",
                      printresult = tdefoutput_pp,
                      testfn = (fn q => quietDefn (TotalDefn.tDefine "foo" q)
                                           (WF_REL_TAC ‘$<’))}
       ‘foo x = if x = 0 then y else foo(x - 1)*2’;

val _  = shouldfail { checkexn = is_struct_HOL_ERR "TotalDefn",
                      printarg = K "qDefine: no schematic defs when \
                                   \termination tac is supplied",
                      printresult = thm_to_string,
                      testfn = (fn q => quietDefn (TotalDefn.qDefine "foo" q)
                                           (SOME (WF_REL_TAC ‘$<’)))}
       ‘foo x = if x = 0 then y else foo(x - 1)*2’;

fun lhs_has_two_args th =
    th |> concl |> strip_forall |> #2 |> lhs |> strip_comb |> #2 |> length
       |> equal 2

val _ = tprint "qDefine/schematic, no termination"
val _ = require_msg (check_result lhs_has_two_args)
                    thm_to_string
                    (fn q => quiet_messages
                               (quietDefn
                                  (TotalDefn.qDefine "foo1[schematic]" q))
                               NONE)
                    ‘foo1 x = if x = 0 then y else foo1(x - 1)*2’;

fun allquiet f x =
    quiet_messages (quiet_warnings (quietDefn f)) x

val _ = tprint "qDefine/schematic, termination"
val _ = require_msg (check_result lhs_has_two_args)
                    thm_to_string
                    (fn q => allquiet
                               (TotalDefn.qDefine "foo2[schematic]" q)
                               (SOME (WF_REL_TAC ‘$<’)))
                    ‘foo2 x = if x = 0 then y else foo2(x - 1)*2’;

val _ = tprint "tailrecDefine (simple recursion: fact2)"
val expected_pat = “!A n. ff A n = if n < 1 then A else ff (A * n) (n - 1)”
fun check1 th =
    case match_term expected_pat (concl th) of
        ([{redex,residue}], []) =>
          aconv redex “ff:num->num->num” andalso
          #1 (dest_const residue) = "fact2"
      | _ => false
fun check2 _ = convtest("fact2 evaluates OK", EVAL, “fact2 1 6”, “720”)
val _ = require_msgk (check_result check1) pp_thm
                     (fn q => TotalDefn.qDefine "fact2_def[tailrecursive]"
                                                q NONE)
                     check2
                     ‘fact2 A n = if n < 1 then A else fact2 (A * n) (n-1)’;

val _ = tprint "tailrecDefine (simple recursion + rebind: fact)"
val expected_pat = “!A n. ff A n = if n < 1 then A else ff (A * n) (n - 1)”
fun check1 th =
    case match_term expected_pat (concl th) of
        ([{redex,residue}], []) =>
          aconv redex “ff:num->num->num” andalso
          #1 (dest_const residue) = "fact"
      | _ => false
fun check2 _ = convtest("fact evaluates OK", EVAL, “fact 1 5”, “120”)
val _ = require_msgk (check_result check1) pp_thm
                     (allquiet
                        (fn q =>
                            TotalDefn.qDefine
                              "fact_def[tailrecursive,allow_rebind]" q NONE))
                     check2
                     ‘fact A n = if n < 1 then A else fact (A * n) (n-1)’;

val _ = tprint "tailrecDefine (2-way mutual recursion)"
val expected_pat = “(!x. ff1 x = if x = 0 then F else ff2 (x + 1)) /\
                    (!n. ff2 n = if n = 0 then T
                                else if n = 1 then F
                                else if n = 2 then T
                                else ff1 (n - 3))”
fun check1 th =
    case match_term expected_pat (concl th) of
        (tms as [rr1,rr2], []) => List.all (is_const o #residue) tms
      | _ => false
fun check2 _ =
    (tprint "DefnBase has record for even";
     require_msgk (check_result Option.isSome) badpp DefnBase.lookup_userdef
                  (fn _ => convtest ("even evaluates OK", EVAL, “even 11”, “F”))
                  “even”)
val _ = require_msgk (check_result check1) pp_thm
                     (allquiet
                        (fn q =>
                            TotalDefn.qDefine
                              "odd_def[tailrecursive]" q NONE))
                     check2
                     ‘(odd x = if x = 0 then F else even (x + 1)) /\
                      (even n = if n = 0 then T
                                    else if n = 1 then F
                                    else if n = 2 then T
                                    else odd (n - 3))’;

val _ = tprint "tailrecDefine (2-way + isolate & nocompute)"
val _ = require_msgk (check_result (K true)) pp_thm
                     (fn q =>
                         TotalDefn.qDefine
                           "urk_def[tailrecursive,nocompute]" q NONE)
                     (fn _ => convtest("urk unevals", EVAL,
                                       “urk x + urk' m”, “urk x + urk' m”))
                     ‘(urk n = urk2 (n + 1)) /\
                      (urk' n = n + 1) /\
                      (urk2 m = if m = 0 then 1 else urk (2 * m))’;
