open HolKernel boolLib bossLib Parse
open EmitTeX combinSyntax PP

fun tprint s = print (StringCvt.padRight #" " 65 s)
fun die() = (print "FAILED!\n"; OS.Process.exit OS.Process.failure)

val _ = tprint "Testing var v2 overridden to v1"
val v1 = mk_var("v1",bool)
val v2 = mk_var("v2",bool)
val s1 = pp_to_string 5 pp_term_as_tex v1
val s2 = pp_to_string 5 (raw_pp_term_as_tex(fn"v2"=>SOME("v1",2)|_=>NONE)) v2
val _ = if s1 = s2 then print "OK\n" else die()

val _ = tprint "Testing const F overridden to T"
val s1 = pp_to_string 5 pp_term_as_tex T
val s2 = pp_to_string 5 (raw_pp_term_as_tex(fn"F"=>SOME("T",1)|_=>NONE)) F
val _ = if s1 = s2 then print "OK\n" else die()

val _ = tprint "Testing syntactic-sugar overriding"
val _ = temp_remove_rules_for_term "~"
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
val _ = if s1 = s2 then print "OK\n" else die()

val _ = tprint "Testing dollarised syntax (/\\)"
val s = pp_to_string 70 pp_term_as_tex conjunction
val _ = if s = "(\\HOLConst{\\HOLTokenConj{}})" then print "OK\n" else die()

val _ = tprint "Testing dollarised syntax (if)"
val s = pp_to_string 70 pp_term_as_tex (mk_var("if", bool))
val _ = if s = "(\\HOLFreeVar{\\HOLKeyword{if}})" then print "OK\n" else die()

open Feedback
val _ = tprint "Testing paren-less dollarised syntax /\\"
val _ = set_trace "EmitTeX: dollar parens" 0
val s = pp_to_string 70 pp_term_as_tex conjunction
val _ = if s = "\\HOLConst{\\HOLTokenConj{}}" then print "OK\n" else die()
val _ = set_trace "EmitTeX: dollar parens" 1

val _ = tprint "Testing UNIV printing (:'a)"
val s = pp_to_string 70 pp_term_as_tex (pred_setSyntax.mk_univ alpha)
val _ = if s = "\\ensuremath{\\cal{U}}(:'a)" then print "OK\n" else die()

val _ = tprint "Testing UNIV printing \"raw\" (:'a)"
val s = pp_to_string 70
                     (raw_pp_term_as_tex (K NONE))
                     (pred_setSyntax.mk_univ alpha)
val _ = if s = "\\ensuremath{\\cal{U}}(:\\ensuremath{\\alpha})" then print "OK\n" else die()

val _ = tprint "Testing UNIV printing (:num)"
val s = pp_to_string 70 pp_term_as_tex (pred_setSyntax.mk_univ numSyntax.num)
val _ = if s = "\\ensuremath{\\cal{U}}(:\\HOLTyOp{num})" then print "OK\n"
        else die()
