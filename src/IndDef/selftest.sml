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

val _ = print "Testing inductive definitions - existential vars\n"

val (rtc'_rules, rtc'_ind, rtc'_cases) = Hol_reln`
  (!x. rtc' r x x) /\
  (!x y. r x y /\ (?z. rtc' r z y) ==> rtc' r x y)
`;

val strongrtc' = derive_strong_induction (rtc'_rules, rtc'_ind)


(* Add EVERY to the standard monoset for inductive relations *)

open Conv boolSyntax Term Tactic Tactical Lib Rewrite bossLib;
open boolTheory listTheory;

val PBETA_CONV = PairRules.PBETA_CONV;

fun GEN_CONV conv :conv = fn tm =>
   let val (v,bdy) = dest_forall tm
   in RAND_CONV (ABS_CONV conv) tm
   end

fun REPEAT_GEN_CONV (conv:conv) :conv = fn tm =>
   if is_forall tm then GEN_CONV (REPEAT_GEN_CONV conv) tm
   else conv tm


val TUPLE_GEN_TAC :tactic = fn (asl,gl) =>
   let val Q = (rator o rand o rand o snd o dest_forall) gl
       val (tpl,bdy) = pairLib.dest_pabs Q
   in pairLib.TUPLE_TAC tpl
      THEN CONV_TAC (REPEAT_GEN_CONV (RAND_CONV
              (RAND_CONV PBETA_CONV THENC
               RATOR_CONV(RAND_CONV PBETA_CONV))))
   end (asl,gl);

val MONO_EVERY = store_thm
  ("MONO_EVERY",
    ``(!x:'a. MEM x l ==> (P x ==> Q x)) ==>
        (EVERY P l ==> EVERY Q l)``,
    Induct_on `l`
    THEN REWRITE_TAC[EVERY_DEF,MEM,DISJ_IMP_THM]
    THEN GEN_TAC
    THEN CONV_TAC (ONCE_DEPTH_CONV FORALL_AND_CONV)
    THEN ONCE_REWRITE_TAC[CONJ_SYM]
    THEN STRIP_TAC
    THEN HO_MATCH_MP_TAC MONO_AND
    THEN CONJ_TAC
    THEN FIRST_ASSUM MATCH_MP_TAC
    THENL [ FIRST_ASSUM MATCH_ACCEPT_TAC, REFL_TAC ]
   );

val MONO_EVERY_TAC =
    HO_MATCH_MP_TAC MONO_EVERY
    THEN TUPLE_GEN_TAC
    THEN CONV_TAC (REPEAT_GEN_CONV (RAND_CONV
           (RAND_CONV(TRY_CONV PBETA_CONV) THENC
            RATOR_CONV(RAND_CONV(TRY_CONV PBETA_CONV)))));

val every_monoset = ("EVERY",MONO_EVERY_TAC) :: InductiveDefinition.bool_monoset;

val _ = print "Testing inductive definitions - extended monoset\n"

val (EC_rules, EC_ind, EC_cases) = prim_Hol_reln every_monoset ``
  (EC r []) /\
  (!a ps. EC r ps ==> EC r ((a,a)::ps)) /\
  (!ps. EVERY (\(a:'a,b). r a b) ps ==> EC r ps)
``;

val strongEC = prim_derive_strong_induction every_monoset (EC_rules, EC_ind)


val _ = OS.Process.exit OS.Process.success


