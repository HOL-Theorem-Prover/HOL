open HolKernel boolLib bossLib Parse
open EmitTeX combinSyntax PP
open testutils

val errcount = ref 0
val _ = diemode := Remember errcount

fun udie() = testutils.die "FAILED!"
fun gotdie s = testutils.die ("\nFAILED: Got >" ^ s ^ "<")

val _ = tprint "Testing var v2 overridden to v1"
val x_t = mk_var("x", alpha)
val v1 = mk_var("v1",bool)
val v2 = mk_var("v2",bool)
val s1 = pp_to_string 5 pp_term_as_tex v1
val s2 = pp_to_string 5 (raw_pp_term_as_tex(fn"v2"=>SOME("v1",2)|_=>NONE)) v2
val _ = if s1 = s2 then OK() else udie()

val _ = tprint "Testing prime var printing"
val v3 = Term.variant [``x:bool``, ``x':bool``, ``x'':bool``] ``x:bool``
val s = pp_to_string 70 pp_term_as_tex v3
val _ = if s = "\\ensuremath{\\HOLFreeVar{x}\\sp{\\prime{}3\\prime{}}}"
        then OK() else gotdie s

val _ = tprint "Testing const F overridden to T"
val s1 = pp_to_string 5 pp_term_as_tex T
val s2 = pp_to_string 5 (raw_pp_term_as_tex(fn"F"=>SOME("T",1)|_=>NONE)) F
val _ = if s1 = s2 then OK() else udie()

val _ = tprint "Testing syntactic-sugar overriding"
val _ = temp_remove_rules_for_term "~"
        (* Note that this is one of the few places where temp_remove_rules_for_term is
           called; tests here are at least somewhat a test of its functionality too. *)
val _ = temp_add_rule {term_name   = "~",
                       fixity      = Prefix 900,
                       pp_elements = [TOK "TOK1"],
                       paren_style = OnlyIfNecessary,
                       block_style = (AroundEachPhrase, (CONSISTENT, 0))}
val _ = temp_add_rule {term_name   = "I",
                       fixity      = Prefix 900,
                       pp_elements = [TOK "TOK2"],
                       paren_style = OnlyIfNecessary,
                       block_style = (AroundEachPhrase, (CONSISTENT, 0))}
val t1 = mk_neg(T)
val t2 = mk_I(T)
val s1 = pp_to_string 5 pp_term_as_tex t1
val s2 = pp_to_string 5 (raw_pp_term_as_tex(fn"TOK2"=>SOME("TOK1",3)|_=>NONE)) t2
val _ = if s1 = s2 then OK() else udie()

val _ = tprint "Testing dollarised syntax (/\\)"
val s = pp_to_string 70 pp_term_as_tex conjunction
val _ = if s = "(\\HOLSymConst{\\HOLTokenConj{}})" then OK() else gotdie s

val _ = tprint "Testing dollarised syntax (if)"
val s = pp_to_string 70 pp_term_as_tex (mk_var("if", bool))
val _ = if s = "(\\HOLFreeVar{\\HOLKeyword{if}})" then OK() else gotdie s

open Feedback
val _ = tprint "Testing paren-less dollarised syntax /\\"
val _ = set_trace "EmitTeX: dollar parens" 0
val s = pp_to_string 70 pp_term_as_tex conjunction
val _ = if s = "\\HOLSymConst{\\HOLTokenConj{}}" then OK() else gotdie s
val _ = set_trace "EmitTeX: dollar parens" 1

val _ = tprint "Testing UNIV printing (:'a)"
val s = pp_to_string 70 pp_term_as_tex (pred_setSyntax.mk_univ alpha)
val _ = if s = "\\ensuremath{{\\cal{U}}}(:\\alpha{})" then OK() else gotdie s

val _ = tprint "Testing UNIV printing \"raw\" (:'a)"
val s = pp_to_string 70
                     (raw_pp_term_as_tex (K NONE))
                     (pred_setSyntax.mk_univ alpha)
val _ = if s = "\\ensuremath{{\\cal{U}}}(:\\ensuremath{\\alpha})" then OK()
        else gotdie s

val _ = tprint "Testing UNIV printing (:num)"
val s = pp_to_string 70 pp_term_as_tex (pred_setSyntax.mk_univ numSyntax.num)
val _ = if s = "\\ensuremath{{\\cal{U}}}(:\\HOLTyOp{num})" then OK()
        else udie()

val _ = tprint "Testing const-annotation for binders"
val P_t = mk_var("P", alpha --> bool)
val s = pp_to_string 70 pp_term_as_tex (mk_forall(x_t, mk_comb(P_t, x_t)))
val _ = if s = "\\HOLSymConst{\\HOLTokenForall{}}\\HOLBoundVar{x}. \\HOLFreeVar{P} \\HOLBoundVar{x}"
        then OK() else gotdie s

val _ = Feedback.emit_MESG := false
fun dtype_test n s = pp_to_string n (raw_pp_theorem_as_tex (fn _ => NONE)) (theorem ("datatype_" ^ s))
val _ = Hol_datatype`foo = C of bool -> 'a -> bool | D of foo => 'a => num list | Econ of foo => foo => 'a`;
val _ = tprint "Testing datatype printing (default)"
val s = dtype_test 55 "foo"
val expected_consistent =
  "\\HOLFreeVar{foo} =\n\
  \    \\HOLConst{C} (\\HOLTyOp{bool} \\HOLTokenMap{} \\ensuremath{\\alpha} \\HOLTokenMap{} \\HOLTyOp{bool})\n\
  \  \\HOLTokenBar{} \\HOLConst{D} (\\ensuremath{\\alpha} \\HOLTyOp{foo}) \\ensuremath{\\alpha} (\\HOLTyOp{num} \\HOLTyOp{list})\n\
  \  \\HOLTokenBar{} \\HOLConst{Econ} (\\ensuremath{\\alpha} \\HOLTyOp{foo}) (\\ensuremath{\\alpha} \\HOLTyOp{foo}) \\ensuremath{\\alpha}"
val _ = if s = expected_consistent then OK()
        else die("Expected\n" ^ expected_consistent ^ "\nGot:\n" ^ s)

val expected_inconsistent =
  "\\HOLFreeVar{foo} = \
  \\\HOLConst{C} (\\HOLTyOp{bool} \\HOLTokenMap{} \\ensuremath{\\alpha} \\HOLTokenMap{} \\HOLTyOp{bool}) \
  \\\HOLTokenBar{} \\HOLConst{D} (\\ensuremath{\\alpha} \\HOLTyOp{foo}) \\ensuremath{\\alpha} (\\HOLTyOp{num} \\HOLTyOp{list})\n\
  \  \\HOLTokenBar{} \\HOLConst{Econ} (\\ensuremath{\\alpha} \\HOLTyOp{foo}) (\\ensuremath{\\alpha} \\HOLTyOp{foo}) \\ensuremath{\\alpha}"
val _ = tprint "Testing datatype printing (compact)"
val s = trace ("EmitTeX: print datatypes compactly", 1)
              (dtype_test 55) "foo"
val _ = if s = expected_inconsistent then OK()
        else die("Expected\n" ^ expected_inconsistent ^ "\nGot:\n" ^ s)


val _ = tprint "Testing enumerated datatype printing"
val _ = Hol_datatype `bar = ETA | ETB | ETC | ETD | ETE | ETF | ETG | ETH | ETI | ETJ`;
val s = dtype_test 20 "bar"
val _ = if s = "\\HOLFreeVar{bar} = \\HOLConst{ETA} \\HOLTokenBar{} \\HOLConst{ETB}\n\
               \    \\HOLTokenBar{} \\HOLConst{ETC} \\HOLTokenBar{} \\HOLConst{ETD}\n\
               \    \\HOLTokenBar{} \\HOLConst{ETE} \\HOLTokenBar{} \\HOLConst{ETF}\n\
               \    \\HOLTokenBar{} \\HOLConst{ETG} \\HOLTokenBar{} \\HOLConst{ETH}\n\
               \    \\HOLTokenBar{} \\HOLConst{ETI} \\HOLTokenBar{} \\HOLConst{ETJ}"
        then
          OK()
        else
          gotdie s

val _ = tprint "Testing d/type printing of a polymorphic (2-field) record type"
val _ = Datatype‘recdtype = <| carrier : 'a set; opn : 'a -> 'b -> 'b |>’
val expected =
    "\\HOLFreeVar{recdtype} = \\HOLTokenLeftrec{} \
    \\\HOLFieldName{carrier} : \
    \\\ensuremath{\\alpha} \\HOLTokenMap{} \\HOLTyOp{bool}; \
    \\\HOLFieldName{opn} : \\ensuremath{\\alpha} \\HOLTokenMap{} \
    \\\ensuremath{\\beta} \\HOLTokenMap{} \\ensuremath{\\beta} \
    \\\HOLTokenRightrec{}"
val _ = require_msg (check_result (equal expected)) String.toString
                    (dtype_test 80) "recdtype"

val _ = tprint "Testing printing of type variables"
val _ = require_msg (check_result (equal "\\alpha{}")) String.toString
                    (pp_to_string 70 pp_type_as_tex) alpha

val _ = tprint "Testing printing of type arrow"
val _ = require_msg (check_result (equal "\\alpha{} \\HOLTokenMap{} \\beta{}"))
                    String.toString
                    (pp_to_string 70 pp_type_as_tex) (alpha --> beta)

val _ = tprint "Testing printing of fn update syntax"
val expected = "\\HOLFreeVar{f}\\llparenthesis\\HOLFreeVar{k} \\HOLTokenMapto{}\
               \ \\HOLFreeVar{v}\\rrparenthesis"
val _ = require_msg (check_result (equal expected)) String.toString
                    (pp_to_string 70 pp_term_as_tex)
                    “f (| k |-> v |)”
val _ = exit_count0 errcount
