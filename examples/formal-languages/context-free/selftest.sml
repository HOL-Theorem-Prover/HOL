open HolKernel Parse boolLib simpLib bossLib
open testutils

local
  open pegLib simpleSexpPEGTheory pegexecTheory
  val ds = derive_compset_distincts ``:sexpNT``
  val {lookups,...} = derive_lookup_ths {pegth = sexpPEG_def, ntty = ``:sexpNT``,
                                   simp = SIMP_CONV (srw_ss())}
  val _ = computeLib.add_funs (ds::lookups)
  val _ = let
    open computeLib
  in
    set_skip the_compset ``evalcase_CASE`` (SOME 1);
    set_skip the_compset ``option_CASE`` (SOME 1);
    set_skip the_compset ``COND`` (SOME 1)
  end
in
fun test0 nt s = let
  val str_t = stringSyntax.fromMLstring s
  val th = EVAL ``peg_exec sexpPEG (pnt ^nt) (MAP (λc. (c, unknown_loc)) (^str_t))
                           [] done failed``
in
  rhs (concl th)
end
end (* local *)

fun test (s, exp) = let
  val exp_t = ``Result (SOME ([], ^exp)) : (char, sexpNT, sexp) evalcase``
in
  tprint (s ^ " --> " ^ term_to_string exp_t);
  require_msg (check_result (aconv exp_t))
              term_to_string (test0 ``sxnt_sexp``)
              s
end
val _ = temp_overload_on ("Ok", ``λt. (Result (SOME ([], t)))``)

val _ = print "\n" before app (ignore o test) [
  ("123", ``123s``),
  ("(123)", ``⟪123⟫``),
  (" (123 10) ", ``⟪123; 10⟫``),
  (" (123 10 (1 2 3)) ", ``⟪ 123; 10; ⟪1; 2; 3⟫ ⟫``),
  (" ( (123   10 ))   ", ``⟪ ⟪ 123; 10 ⟫ ⟫``),
  ("'(1 2)", ``’ ⟪1; 2⟫``),
  ("(1(2(3)))", ``⟪1; ⟪ 2; ⟪ 3 ⟫ ⟫ ⟫``),
  ("'1", ``’ 1``),
  ("foo", ``SX_SYM "foo"``),
  ("(foo)", ``⟪SX_SYM "foo"⟫``),
  ("()", ``nil``),
  ("(foo )", ``⟪SX_SYM "foo"⟫``),
  ("foo2", ``SX_SYM "foo2"``),
  ("(foo bar 3 4)", ``⟪ SX_SYM "foo"; SX_SYM "bar"; 3; 4 ⟫``),
  ("(1 2 3 . 4)", ``SX_CONS 1 (SX_CONS 2 (SX_CONS 3 4))``),
  ("(1 . (2 . (3 . 4)))", ``SX_CONS 1 (SX_CONS 2 (SX_CONS 3 4))``),
  ("(3 . 4)", ``SX_CONS 3 4``),
  ("\"foo bar\"", ``SX_STR "foo bar"``),
  ("( \" foo \"  \"bar\" )", ``⟪ SX_STR " foo "; SX_STR "bar" ⟫``),
  ("\"foo\\\"\"", ``SX_STR "foo\""``),
  ("\"foo\\\\\"", ``SX_STR "foo\\"``),
  ("(1sym)", ``⟪1; SX_SYM "sym"⟫``),
  ("symq\"9", ``SX_SYM "symq\"9"``),
  ("symd.9", ``SX_SYM "symd.9"``)
]

val _ = app tpp ["⟪2; 3⟫", "⟪ ⟫", "⟪SX_SYM \"foo\"⟫", "⟪ ⟪3 • 4⟫; ⟪3; 4⟫ ⟫"]

val _ = tprint "Can EVAL ptree_size"
val _ = require_msg (check_result (aconv “1n” o rhs o concl))
                    (term_to_string o rhs o concl)
                    EVAL “ptree_size (Lf x)”
local
  val t = “TOK 1n”
  val _ = tprint "Can EVAL ptree_fringe"
in
val _ = require_msg (check_result (aconv “[^t]” o rhs o concl))
                    (term_to_string o rhs o concl)
                    EVAL “ptree_fringe (Lf (^t,x))”
end
