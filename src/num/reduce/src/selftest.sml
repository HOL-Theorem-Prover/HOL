open boolLib reduceLib Arithconv
open testutils

val _ = app (fn (n,c,t) => convtest(n,c,lhs t,rhs t)) [
  ("ADD_CONV", ADD_CONV, “4 + 5 = 9”),
  ("SBC_CONV(1)", SBC_CONV, “4-5 = 0”),
  ("SBC_CONV(2)", SBC_CONV, “13-4 = 9”),
  ("SUC_CONV(1)", SUC_CONV, “SUC 10 = 11”),
  ("SUC_CONV(2)", SUC_CONV, “SUC 0 = 1”),
  ("PRE_CONV(1)", PRE_CONV, “PRE 0 = 0”),
  ("PRE_CONV(2)", PRE_CONV, “PRE 12 = 11”),
  ("MUL_CONV(1)", MUL_CONV, “3 * 4 = 12”),
  ("MUL_CONV(2)", MUL_CONV, “0 * 4 = 0”),
  ("MUL_CONV(3)", MUL_CONV, “4 * 0 = 0”),
  ("MOD_CONV(1)", MOD_CONV, “3 MOD 10 = 3”),
  ("MOD_CONV(2)", MOD_CONV, “14 MOD 9 = 5”),
  ("MOD_CONV(3)", MOD_CONV, “0 MOD 10 = 0”),
  (* NOTE: the old Arithconv doesn't support this:
  ("MOD_CONV(4)", MOD_CONV, “4 MOD 0 = 4”),
  ("MOD_CONV(5)", MOD_CONV, “0 MOD 0 = 0”),
   *)
  ("DIV_CONV(1)", DIV_CONV, “20 DIV 4 = 5”),
  ("DIV_CONV(2)", DIV_CONV, “20 DIV 3 = 6”),
  ("DIV_CONV(3)", DIV_CONV, “1 DIV 4 = 0”),
  ("DIV_CONV(4)", DIV_CONV, “0 DIV 4 = 0”),
  (* NOTE: the old Arithconv doesn't support this:
  ("DIV_CONV(5)", DIV_CONV, “20 DIV 0 = 0”),
  ("DIV_CONV(6)", DIV_CONV, “0 DIV 0 = 0”),
   *)
  ("EXP_CONV(1)", EXP_CONV, “2 EXP 6 = 64”),
  ("EXP_CONV(2)", EXP_CONV, “1 EXP 10 = 1”),
  ("LT_CONV(1)", LT_CONV, “3 < 4 <=> T”),
  ("LT_CONV(2)", LT_CONV, “5 < 5 <=> F”),
  ("LT_CONV(3)", LT_CONV, “10 < 5 <=> F”),
  ("LT_CONV(4)", LT_CONV, “10 < 0 <=> F”),
  ("EVEN_CONV(1)", EVEN_CONV, “EVEN 106 <=> T”),
  ("EVEN_CONV(2)", EVEN_CONV, “EVEN 103 <=> F”),
  ("EVEN_CONV(3)", EVEN_CONV, “EVEN 0 <=> T”),
  ("ODD_CONV(1)", ODD_CONV, “ODD 106 <=> F”),
  ("ODD_CONV(2)", ODD_CONV, “ODD 103 <=> T”),
  ("ODD_CONV(3)", ODD_CONV, “ODD 0 <=> F”),

  ("NOT_CONV(1)", NOT_CONV, “~T <=> F”),
  ("NOT_CONV(2)", NOT_CONV, “~F <=> T”),
  ("NOT_CONV(3)", NOT_CONV, “~~p <=> p”),
  ("NOT_CONV(4)", NOT_CONV, “~~~q <=> ~q”)
]
