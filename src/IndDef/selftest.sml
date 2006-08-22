open IndDefLib IndDefRules arithmeticTheory

val _ = print "Testing inductive definitions - mutual recursion\n"

val (oe_rules, oe_ind, oe_cases) = Hol_reln`
  even 0 /\
  (!m. odd m /\ 1 <= m ==> even (m + 1)) /\
  (!m. even m ==> odd (m + 1))
`;

val strongoe = derive_strong_induction (oe_rules, oe_ind)

val _ = print "Testing inductive definitions - scheme variables\n"

val (rtc_rules, rtc_ind, rtc_cases) = Hol_reln`
  (!x. rtc r x x) /\
  (!x y z. rtc r x y /\ r y z ==> rtc r x z)
`;

val strongrtc = derive_strong_induction (rtc_rules, rtc_ind)

val _ = OS.Process.exit OS.Process.success


