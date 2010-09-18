open HolKernel Parse boolLib IndDefLib

fun die s = (if !Globals.interactive then
               raise Fail s
             else print (s^"\n"); OS.Process.exit OS.Process.failure)
fun checkhyps th = if null (hyp th) then ()
                   else die "FAILED - Hyps in theorem!"

fun derive_strong_induction p =
    (IndDefLib.derive_strong_induction p
     handle HOL_ERR _ => die "FAILED to prove strong induction!";
     print "Proved strong induction\n")

(* set up a fake arithmetic theory *)
val _ = new_type ("num", 0)
val _ = new_constant("Z", ``:num``)
val _ = new_constant("ONE", ``:num``)
val _ = new_constant("TWO", ``:num``)
val _ = new_constant("FOUR", ``:num``)
val _ = new_constant("<=", ``:num -> num -> bool``)
val _ = set_fixity "<=" (Infix(NONASSOC, 450))
val _ = new_constant("<", ``:num -> num -> bool``)
val _ = set_fixity "<" (Infix(NONASSOC, 450))
val _ = new_constant ("+", ``:num -> num -> num``)
val _ = set_fixity "+" (Infixl 500)
val _ = new_constant ("*", ``:num -> num -> num``)
val _ = set_fixity "*" (Infixl 600)
val _ = new_constant ("SUC", ``:num -> num``)


val _ = print "*** Testing inductive definitions - mutual recursion\n"


val (oe_rules, oe_ind, oe_cases) = Hol_reln`
  even Z /\
  (!m. odd m /\ ONE <= m ==> even (m + ONE)) /\
  (!m. even m ==> odd (m + ONE))
`;
val _ = checkhyps oe_rules

val strongoe = derive_strong_induction (oe_rules, oe_ind)

val _ = print "*** Testing inductive definitions - scheme variables\n"

val (rtc_rules, rtc_ind, rtc_cases) = Hol_reln`
  (!x. rtc r x x) /\
  (!x y z. rtc r x y /\ r y z ==> rtc r x z)
`;
val _ = checkhyps rtc_rules

val _ = print "*** Testing schematic variables for multiple relations\n"
val (mscheme_rules, mscheme_ind, mscheme_cases) = Hol_reln`
  (!n m. n < m ==> foo P n m) /\
  (!n m. P n ==> foo P n m) /\
  (!n m. bar P n ==> foo P n m) /\
  (!n. FOUR < n ==> bar P (TWO * n))
`
val _ = checkhyps mscheme_rules

val strongrtc = derive_strong_induction (rtc_rules, rtc_ind)

val _ = print "*** Testing inductive definitions - existential vars\n"

val (rtc'_rules, rtc'_ind, rtc'_cases) = Hol_reln`
  (!x. rtc' r x x) /\
  (!x y. r x y /\ (?z. rtc' r z y) ==> rtc' r x y)
`;
val _ = checkhyps rtc'_rules

val strongrtc' = derive_strong_induction (rtc'_rules, rtc'_ind)

(* emulate the example in examples/opsemScript.sml *)
val _ = print "*** Testing opsem example\n"
val _ = new_type ("comm", 0)
val _ = new_constant("Skip", ``:comm``)
val _ = new_constant("::=", ``:num -> ((num -> num) -> num) -> comm``)
val _ = new_constant(";;", ``:comm -> comm -> comm``)
val _ = new_constant("If", ``:((num -> num) -> bool) -> comm -> comm -> comm``)
val _ = new_constant("While", ``:((num -> num) -> bool) -> comm -> comm``)
val _ = set_fixity "::=" (Infixr 400);
val _ = set_fixity ";;"  (Infixr 350);

val (rules,induction,ecases) = Hol_reln
     `(!s. EVAL Skip s s)
 /\   (!s V E. EVAL (V ::= E) s (\v. if v=V then E s else s v))
 /\   (!C1 C2 s1 s3.
        (?s2. EVAL C1 s1 s2 /\ EVAL C2 s2 s3) ==> EVAL (C1;;C2) s1 s3)
 /\   (!C1 C2 s1 s2 B. EVAL C1 s1 s2 /\  B s1 ==> EVAL (If B C1 C2) s1 s2)
 /\   (!C1 C2 s1 s2 B. EVAL C2 s1 s2 /\ ~B s1 ==> EVAL (If B C1 C2) s1 s2)
 /\   (!C s B.                           ~B s ==> EVAL (While B C) s s)
 /\   (!C s1 s3 B.
        (?s2. EVAL C s1 s2 /\
              EVAL (While B C) s2 s3 /\ B s1) ==> EVAL (While B C) s1 s3)`;

val _ = checkhyps rules

val strongeval = derive_strong_induction(rules, induction)

(* emulate the example in examples/monosetScript.sml *)
val _ = print "*** Testing monoset example\n"
val _ = new_type ("t", 0)
val _ = new_type ("list", 1)
val _ = new_constant ("v", ``:num -> t``)
val _ = new_constant ("app", ``:t list -> t``)
val _ = new_constant ("EVERY", ``:('a -> bool) -> 'a list -> bool``)
val _ = new_constant ("MEM", ``:'a -> 'a list -> bool``)
val _ = new_constant ("ZIP", ``:('a list # 'b list) -> ('a # 'b) list``)

val MONO_EVERY = mk_thm([], ``(!x:'a. P x ==> Q x) ==>
                              (EVERY P l ==> EVERY Q l)``)
val _ = add_mono_thm MONO_EVERY

val (red_rules, red_ind, red_cases) = Hol_reln `
  (!n. red f (v n) (v (f n))) /\
  (!t0s ts. EVERY (\ (t0,t). red f t0 t) (ZIP (t0s, ts)) ==>
            red f (app t0s) (app ts))
`;
val _ = checkhyps red_rules

val strongred = derive_strong_induction (red_rules, red_ind);

(* emulate Peter's example *)
val _ = print "*** Testing Peter's example\n"
val _ = new_constant ("nil", ``:'a list``)
val _ = new_constant ("cons", ``:'a -> 'a list -> 'a list``)
val _ = new_constant ("HD", ``:'a list -> 'a``)
val _ = new_constant ("TL", ``:'a list -> 'a list``)
val (ph_rules, ph_ind, ph_cases) = Hol_reln`
  (WF_CX nil) /\
  (!s ty cx. WF_CX cx /\ WF_TYPE cx ty ==> WF_CX (cons (s,ty) cx)) /\

  (!n cx. WF_CX cx ==> WF_TYPE cx (v n)) /\
  (!ts cx s. WF_CX cx /\ MEM (s, HD ts) cx /\ EVERY (\t. WF_TYPE cx t) ts /\
             red SUC (HD ts) (HD (TL ts)) ==>
             WF_TYPE cx (app ts))
`
val _ = checkhyps ph_rules

val ph_strong = derive_strong_induction(ph_rules, ph_ind)

(* UNCURRY with more than two arguments *)
val _ = print "*** Testing UNCURRY with more than two arguments\n"
val (u3_rules, u3_ind, u3_cases) = Hol_reln`
  u3 (Z,ONE,TWO) /\
  (!x y z. (\ ((x,y), z). u3 (x,y,z)) ((y,x),z) ==> u3 (x,y,z))
`
val _ = checkhyps u3_rules
val u3_strong = derive_strong_induction(u3_rules, u3_ind)

(* single rule *)
val _ = print "*** Testing strong principle for singleton rule\n"
val (single_rules, single_ind, single_cases) = Hol_reln`
  (!x y. RTC single x y \/ (x = y + TWO) ==> single x y)
`;
val _ = checkhyps single_rules

val _ = derive_strong_induction(single_rules, single_ind)

val _ = OS.Process.exit OS.Process.success
