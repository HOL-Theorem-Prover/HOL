(*===========================================================================*)
(* Construct positive (nonzero) rationals from natural numbers               *)
(*===========================================================================*)

structure hratScript =
struct

open HolKernel boolLib;
infix THEN THENL ORELSE;

(*
app load ["hol88Lib",
          "numLib",
          "reduceLib",
          "pairLib",
          "arithmeticTheory",
          "quotient",
          "jrhUtils"];
*)

open Parse boolLib hol88Lib numLib reduceLib
     pairLib PairedLambda pairTheory
     arithmeticTheory numTheory prim_recTheory jrhUtils;

val _ = new_theory "hrat";

(*---------------------------------------------------------------------------*)
(* The following tactic gets rid of "PRE"s by implicitly bubbling out "SUC"s *)
(* from sums and products - more complex terms may leave extra subgoals.     *)
(*---------------------------------------------------------------------------*)

val UNSUCK_TAC =
 let val tac = W(MAP_EVERY (STRUCT_CASES_TAC o C SPEC num_CASES) o frees o snd)
               THEN REWRITE_TAC[NOT_SUC, PRE, MULT_CLAUSES, ADD_CLAUSES]
     val [sps, azero, mzero] = map (C (curry prove) tac)
       [(--`~(x = 0) ==> (SUC(PRE x) = x)`--),
        (--`(x + y = 0) = (x = 0) /\ (y = 0)`--),
        (--`(x * y = 0) = (x = 0) \/ (y = 0)`--)] in
 REPEAT (IMP_SUBST_TAC sps THENL
         [REWRITE_TAC[azero, mzero, NOT_SUC], ALL_TAC]) end;

(*---------------------------------------------------------------------------*)
(* Definitions of operations on representatives                              *)
(*---------------------------------------------------------------------------*)

val trat_1 = new_definition("trat_1",
  (--`trat_1 = (0,0)`--));

val trat_inv = new_definition("trat_inv",
  (--`trat_inv (x:num,(y:num)) = (y,x)`--));

val trat_add = new_infixl_definition("trat_add",
  --`trat_add (x,y) (x',y') =
    (PRE(((SUC x)*(SUC y')) + ((SUC x')*(SUC y))),
     PRE((SUC y)*(SUC y')))`--,
    500);

val trat_mul = new_infixl_definition("trat_mul",
  (--`trat_mul (x,y) (x',y') =
    (PRE((SUC x)*(SUC x')),
     PRE((SUC y)*(SUC y')))`--), 600);

val trat_sucint = new_recursive_definition
  {name = "trat_sucint",
   def = --`(trat_sucint 0 = trat_1) /\
              (trat_sucint (SUC n) = (trat_sucint n) trat_add trat_1)`--,
   rec_axiom = num_Axiom}

(*---------------------------------------------------------------------------*)
(* Definition of the equivalence relation, and proof that it *is* one        *)
(*---------------------------------------------------------------------------*)

val trat_eq = new_definition("trat_eq",
  (--`trat_eq (x,y) (x',y') =
    (SUC x * SUC y' = SUC x' * SUC y)`--));
val _ = temp_set_fixity "trat_eq" (Infix(NONASSOC, 450))

val TRAT_EQ_REFL = store_thm("TRAT_EQ_REFL",
  (--`!p. p trat_eq p`--),
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[trat_eq]
  THEN REFL_TAC);

val TRAT_EQ_SYM = store_thm("TRAT_EQ_SYM",
  (--`!p q. (p trat_eq q) = (q trat_eq p)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[trat_eq]
  THEN CONV_TAC(RAND_CONV SYM_CONV) THEN REFL_TAC);

val TRAT_EQ_TRANS = store_thm("TRAT_EQ_TRANS",
  (--`!p q r. p trat_eq q /\ q trat_eq r ==> p trat_eq r`--),
  let val th = (GEN_ALL o fst o EQ_IMP_RULE o SPEC_ALL) MULT_SUC_EQ in
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[trat_eq] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_MP_TAC th THEN EXISTS_TAC (--`SND(q:num#num)`--) THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  POP_ASSUM(CONJUNCTS_THEN2 SUBST1_TAC (SUBST1_TAC o SYM)) THEN
  CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM)) end);

val TRAT_EQ_AP = store_thm("TRAT_EQ_AP",
  (--`!p q. (p = q) ==> (p trat_eq q)`--),
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_ACCEPT_TAC TRAT_EQ_REFL);

(*---------------------------------------------------------------------------*)
(* Prove that the operations are all well-defined                            *)
(*---------------------------------------------------------------------------*)

val TRAT_ADD_SYM_EQ = store_thm("TRAT_ADD_SYM_EQ",
  (--`!h i. (h trat_add i) =(i trat_add h)`--),
  REPEAT GEN_PAIR_TAC THEN
  PURE_REWRITE_TAC[trat_add, PAIR_EQ] THEN CONJ_TAC THEN
  AP_TERM_TAC THEN TRY (MATCH_ACCEPT_TAC MULT_SYM) THEN
  GEN_REWR_TAC RAND_CONV [ADD_SYM]
  THEN REFL_TAC);

val TRAT_MUL_SYM_EQ = store_thm("TRAT_MUL_SYM_EQ",
  (--`!h i. h trat_mul i = i trat_mul h`--),
  REPEAT GEN_PAIR_TAC THEN
  PURE_REWRITE_TAC[trat_mul, PAIR_EQ] THEN CONJ_TAC THEN
  AP_TERM_TAC THEN TRY (MATCH_ACCEPT_TAC MULT_SYM) THEN
  GEN_REWR_TAC RAND_CONV [MULT_SYM] THEN REFL_TAC);

val TRAT_INV_WELLDEFINED = store_thm("TRAT_INV_WELLDEFINED",
  (--`!p q. p trat_eq q ==> (trat_inv p) trat_eq (trat_inv q)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[trat_inv, trat_eq] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  POP_ASSUM(ACCEPT_TAC o SYM));

val TRAT_ADD_WELLDEFINED = store_thm("TRAT_ADD_WELLDEFINED",
  (--`!p q r. p trat_eq q ==> (p trat_add r) trat_eq (q trat_add r)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[trat_add, trat_eq] THEN DISCH_TAC
  THEN UNSUCK_TAC THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN BINOP_TAC THENL
   [REWRITE_TAC[MULT_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    REWRITE_TAC[MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC,
    CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM))]);

val TRAT_ADD_WELLDEFINED2 = store_thm("TRAT_ADD_WELLDEFINED2",
  (--`!p1 p2 q1 q2. (p1 trat_eq p2) /\ (q1 trat_eq q2)
        ==> (p1 trat_add q1) trat_eq (p2 trat_add q2)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TRAT_EQ_TRANS THEN
  EXISTS_TAC (--`p1 trat_add q2`--) THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TRAT_ADD_SYM_EQ], ALL_TAC] THEN
  MATCH_MP_TAC TRAT_ADD_WELLDEFINED THEN ASM_REWRITE_TAC[]);

val TRAT_MUL_WELLDEFINED = store_thm("TRAT_MUL_WELLDEFINED",
  (--`!p q r. p trat_eq q ==> (p trat_mul r) trat_eq (q trat_mul r)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[trat_eq, trat_mul] THEN DISCH_TAC
  THEN UNSUCK_TAC THEN REWRITE_TAC[MULT_ASSOC] THEN AP_THM_TAC THEN
  AP_TERM_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  REWRITE_TAC[MULT_ASSOC] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);

val TRAT_MUL_WELLDEFINED2 = store_thm("TRAT_MUL_WELLDEFINED2",
  (--`!p1 p2 q1 q2. (p1 trat_eq p2) /\ (q1 trat_eq q2)
        ==> (p1 trat_mul q1) trat_eq (p2 trat_mul q2)`--),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC TRAT_EQ_TRANS THEN
  EXISTS_TAC (--`p1 trat_mul q2`--) THEN
  CONJ_TAC THENL [ONCE_REWRITE_TAC[TRAT_MUL_SYM_EQ], ALL_TAC] THEN
  MATCH_MP_TAC TRAT_MUL_WELLDEFINED THEN ASM_REWRITE_TAC[]);

(*---------------------------------------------------------------------------*)
(* Now theorems for the representatives.                                     *)
(*---------------------------------------------------------------------------*)

val TRAT_ADD_SYM = store_thm("TRAT_ADD_SYM",
  (--`!h i. (h trat_add i) trat_eq (i trat_add h)`--),
  REPEAT GEN_TAC THEN MATCH_MP_TAC TRAT_EQ_AP THEN
  MATCH_ACCEPT_TAC TRAT_ADD_SYM_EQ);

val TRAT_ADD_ASSOC = store_thm("TRAT_ADD_ASSOC",
  (--`!h i j. (h trat_add (i trat_add j)) trat_eq ((h trat_add i) trat_add j)`--),
  REPEAT GEN_PAIR_TAC THEN  MATCH_MP_TAC TRAT_EQ_AP THEN
  PURE_REWRITE_TAC[trat_add]
  THEN UNSUCK_TAC THEN REWRITE_TAC[PAIR_EQ, GSYM MULT_ASSOC,
    GSYM ADD_ASSOC, RIGHT_ADD_DISTRIB] THEN REPEAT AP_TERM_TAC THEN
  CONV_TAC(DEPTH_CONV(SYM_CANON_CONV MULT_SYM
   (fn (a,b) => fst(dest_var(rand(rand a))) < fst(dest_var(rand(rand b))))
  )) THEN REFL_TAC);

val TRAT_MUL_SYM = store_thm("TRAT_MUL_SYM",
  (--`!h i. ($trat_mul h i) trat_eq ($trat_mul i h)`--),
  REPEAT GEN_TAC THEN MATCH_MP_TAC TRAT_EQ_AP THEN
  MATCH_ACCEPT_TAC TRAT_MUL_SYM_EQ);

val TRAT_MUL_ASSOC = store_thm("TRAT_MUL_ASSOC",
  (--`!h i j. ($trat_mul h ($trat_mul i j)) trat_eq ($trat_mul ($trat_mul h i) j)`--),
  REPEAT GEN_PAIR_TAC THEN MATCH_MP_TAC TRAT_EQ_AP THEN
  PURE_REWRITE_TAC[trat_mul] THEN
  UNSUCK_TAC THEN REWRITE_TAC[PAIR_EQ, MULT_ASSOC]);

val TRAT_LDISTRIB = store_thm("TRAT_LDISTRIB",
  (--`!h i j. ($trat_mul h ($trat_add i j)) trat_eq
              ($trat_add ($trat_mul h i) ($trat_mul h j))`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[trat_mul, trat_add, trat_eq] THEN
  UNSUCK_TAC THEN REWRITE_TAC[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]
  THEN BINOP_TAC THEN CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM)));

val TRAT_MUL_LID = store_thm("TRAT_MUL_LID",
  (--`!h. ($trat_mul trat_1 h) trat_eq h`--),
  GEN_PAIR_TAC THEN MATCH_MP_TAC TRAT_EQ_AP THEN
  PURE_REWRITE_TAC[trat_1, trat_mul] THEN
  REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, PRE]);

val TRAT_MUL_LINV = store_thm("TRAT_MUL_LINV",
  (--`!h. ($trat_mul (trat_inv h) h) trat_eq trat_1`--),
  GEN_PAIR_TAC THEN PURE_REWRITE_TAC[trat_1, trat_inv, trat_mul, trat_eq]
  THEN UNSUCK_TAC THEN CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM)));

val TRAT_NOZERO = store_thm("TRAT_NOZERO",
  (--`!h i. ~(($trat_add h i) trat_eq h)`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[trat_add, trat_eq] THEN
  UNSUCK_TAC THEN REWRITE_TAC[RIGHT_ADD_DISTRIB, GSYM MULT_ASSOC] THEN
  GEN_REWR_TAC (funpow 3 RAND_CONV) [MULT_SYM] THEN
  REWRITE_TAC[ADD_INV_0_EQ] THEN
  REWRITE_TAC[MULT_CLAUSES, ADD_CLAUSES, NOT_SUC]);

val TRAT_ADD_TOTAL = store_thm("TRAT_ADD_TOTAL",
  (--`!h i. (h trat_eq i) \/
         (?d. h trat_eq (i trat_add d)) \/
         (?d. i trat_eq (h trat_add d))`--),
  REPEAT GEN_PAIR_TAC THEN PURE_REWRITE_TAC[trat_eq, trat_add] THEN
  W(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o C SPECL LESS_LESS_CASES o
    snd o strip_comb o find_term is_eq o snd) THEN
  PURE_ASM_REWRITE_TAC[] THEN TRY(DISJ1_TAC THEN REFL_TAC) THEN DISJ2_TAC
  THENL [DISJ2_TAC, DISJ1_TAC] THEN POP_ASSUM(X_CHOOSE_TAC (--`p:num`--) o
  REWRITE_RULE[GSYM ADD1] o MATCH_MP LESS_ADD_1) THEN
  EXISTS_TAC (--`(p:num,PRE(SUC(SND(h:num#num)) * SUC(SND(i:num#num))))`--) THEN
  PURE_REWRITE_TAC[trat_add, trat_eq] THEN UNSUCK_TAC THEN
  REWRITE_TAC[MULT_ASSOC] THEN POP_ASSUM SUBST1_TAC THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN BINOP_TAC THEN
  CONV_TAC(AC_CONV(MULT_ASSOC,MULT_SYM)));

val TRAT_SUCINT_0 = store_thm("TRAT_SUCINT_0",
(--`!n. (trat_sucint n) trat_eq (n,0)`--),
INDUCT_TAC THEN REWRITE_TAC[trat_sucint, trat_1, TRAT_EQ_REFL] THEN
  MATCH_MP_TAC TRAT_EQ_TRANS THEN EXISTS_TAC (--`(n,0) trat_add (0,0)`--) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC TRAT_ADD_WELLDEFINED THEN POP_ASSUM ACCEPT_TAC,
    REWRITE_TAC[trat_add, trat_eq] THEN UNSUCK_TAC THEN
    (* for new term nets  REWRITE_TAC[SYM(num_CONV (--`1`--))] *)
    REWRITE_TAC[MULT_CLAUSES,ADD_CLAUSES]]);

(* Proof changed for new term nets *)
val TRAT_ARCH = store_thm("TRAT_ARCH",
(--`!h. ?n. ?d. (trat_sucint n) trat_eq (h trat_add d)`--),
 GEN_PAIR_TAC THEN EXISTS_TAC (--`SUC(FST(h:num#num))`--) THEN
  EXISTS_TAC(--`(PRE((SUC(SUC(FST h))*(SUC(SND h))) - (SUC(FST h))),SND h)`--)
  THEN MATCH_MP_TAC TRAT_EQ_TRANS THEN
  EXISTS_TAC (--`(SUC(FST(h:num#num)),0)`--)
  THEN PURE_REWRITE_TAC[TRAT_SUCINT_0] THEN PURE_REWRITE_TAC[trat_add, trat_eq]
  THEN REWRITE_TAC[] THEN UNSUCK_TAC THENL
   [REWRITE_TAC[SUB_EQ_0, GSYM NOT_LESS],
    REWRITE_TAC [RIGHT_SUB_DISTRIB,
        RIGHT_ADD_DISTRIB,SYM(num_CONV (--`1`--)), MULT_RIGHT_1] THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN IMP_SUBST_TAC SUB_ADD THEN
    REWRITE_TAC[MULT_ASSOC] THEN MATCH_MP_TAC LESS_MONO_MULT THEN
   MATCH_MP_TAC LESS_IMP_LESS_OR_EQ] THEN
  W(C (curry SPEC_TAC) (--`x:num`--) o rand o rator o snd) THEN GEN_TAC THEN
  REWRITE_TAC [MULT_SUC,GSYM ADD_ASSOC,ADD1] THEN
  MATCH_MP_TAC LESS_ADD_NONZERO THEN
  REWRITE_TAC[ADD_CLAUSES, NOT_SUC, ONCE_REWRITE_RULE[ADD_SYM] (GSYM ADD1)]);

(* original
  REWRITE_TAC[MULT_CLAUSES, GSYM ADD_ASSOC] THEN MATCH_MP_TAC LESS_ADD_NONZERO
  THEN REWRITE_TAC[ADD_CLAUSES, NOT_SUC]
*)
val TRAT_SUCINT = store_thm("TRAT_SUCINT",
  (--`((trat_sucint 0) trat_eq trat_1) /\
   (!n. (trat_sucint(SUC n)) trat_eq ((trat_sucint n) trat_add trat_1))`--),
  CONJ_TAC THEN TRY GEN_TAC THEN MATCH_MP_TAC TRAT_EQ_AP THEN
  REWRITE_TAC[trat_sucint]);

(*---------------------------------------------------------------------------*)
(* Define type of and functions over the equivalence classes                 *)
(*---------------------------------------------------------------------------*)

val TRAT_EQ_EQUIV = store_thm("TRAT_EQ_EQUIV",
  (--`!p q. p trat_eq q = ($trat_eq p = $trat_eq q)`--),
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  CONV_TAC (ONCE_DEPTH_CONV (X_FUN_EQ_CONV (--`r:num#num`--))) THEN
  EQ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC (--`q:num#num`--)) THEN
      REWRITE_TAC[TRAT_EQ_REFL],
      DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
       [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[TRAT_EQ_SYM]), ALL_TAC] THEN
      POP_ASSUM(fn th => DISCH_THEN(MP_TAC o CONJ th)) THEN
      MATCH_ACCEPT_TAC TRAT_EQ_TRANS]);

val [HRAT_ADD_SYM, HRAT_ADD_ASSOC, HRAT_MUL_SYM, HRAT_MUL_ASSOC,
     HRAT_LDISTRIB, HRAT_MUL_LID, HRAT_MUL_LINV, HRAT_NOZERO,
     HRAT_ADD_TOTAL, HRAT_ARCH, HRAT_SUCINT] =
  quotient.define_equivalence_type
    {name = "hrat",
     equiv = TRAT_EQ_EQUIV, defs =
     [{def_name="hrat_1",   fname="hrat_1",
       func=Term`trat_1`, fixity=Prefix},
      {def_name="hrat_inv", fname="hrat_inv",
       func=Term`trat_inv`, fixity=Prefix},
      {def_name="hrat_add", fname="hrat_add",
       func=Term`$trat_add`, fixity=Infixl 500},
      {def_name="hrat_mul", fname="hrat_mul",
       func=Term`$trat_mul`, fixity=Infixl 600},
      {def_name="hrat_sucint", fname="hrat_sucint",
       func=Term`trat_sucint`, fixity=Prefix}],
     welldefs = [TRAT_INV_WELLDEFINED, TRAT_ADD_WELLDEFINED2,
                 TRAT_MUL_WELLDEFINED2],
     old_thms = [TRAT_ADD_SYM, TRAT_ADD_ASSOC, TRAT_MUL_SYM, TRAT_MUL_ASSOC,
                 TRAT_LDISTRIB, TRAT_MUL_LID, TRAT_MUL_LINV, TRAT_NOZERO,
                 TRAT_ADD_TOTAL, TRAT_ARCH, TRAT_SUCINT]};

(*---------------------------------------------------------------------------*)
(* Save theorems and make sure they are all of the right form                *)
(*---------------------------------------------------------------------------*)

val HRAT_ADD_SYM = store_thm("HRAT_ADD_SYM",
  (--`!h i. h hrat_add i = i hrat_add h`--),
  MATCH_ACCEPT_TAC HRAT_ADD_SYM);

val HRAT_ADD_ASSOC = store_thm("HRAT_ADD_ASSOC",
  (--`!h i j. h hrat_add (i hrat_add j) = (h hrat_add i) hrat_add j`--),
  MATCH_ACCEPT_TAC HRAT_ADD_ASSOC);

val HRAT_MUL_SYM = store_thm("HRAT_MUL_SYM",
  (--`!h i. h hrat_mul i = i hrat_mul h`--),
  MATCH_ACCEPT_TAC HRAT_MUL_SYM);

val HRAT_MUL_ASSOC = store_thm("HRAT_MUL_ASSOC",
  (--`!h i j. h hrat_mul (i hrat_mul j) = (h hrat_mul i) hrat_mul j`--),
  MATCH_ACCEPT_TAC HRAT_MUL_ASSOC);

val HRAT_LDISTRIB = store_thm("HRAT_LDISTRIB",
  (--`!h i j. h hrat_mul (i hrat_add j) = (h hrat_mul i) hrat_add (h hrat_mul j)`--),
  MATCH_ACCEPT_TAC HRAT_LDISTRIB);

val HRAT_MUL_LID = store_thm("HRAT_MUL_LID",
  (--`!h. hrat_1 hrat_mul h = h`--),
  MATCH_ACCEPT_TAC HRAT_MUL_LID);

val HRAT_MUL_LINV = store_thm("HRAT_MUL_LINV",
  (--`!h. (hrat_inv h) hrat_mul h = hrat_1`--),
  MATCH_ACCEPT_TAC HRAT_MUL_LINV);

val HRAT_NOZERO = store_thm("HRAT_NOZERO",
  (--`!h i. ~(h hrat_add i = h)`--),
  MATCH_ACCEPT_TAC HRAT_NOZERO);

val HRAT_ADD_TOTAL = store_thm("HRAT_ADD_TOTAL",
  (--`!h i. (h = i) \/ (?d. h = i hrat_add d) \/ (?d. i = h hrat_add d)`--),
  MATCH_ACCEPT_TAC HRAT_ADD_TOTAL);

val HRAT_ARCH = store_thm("HRAT_ARCH",
  (--`!h. ?n d. hrat_sucint n = h hrat_add d`--),
  MATCH_ACCEPT_TAC HRAT_ARCH);

val HRAT_SUCINT = store_thm("HRAT_SUCINT",
  (--`((hrat_sucint 0) = hrat_1) /\
   (!n. hrat_sucint(SUC n) = (hrat_sucint n) hrat_add hrat_1)`--),
  MATCH_ACCEPT_TAC HRAT_SUCINT);

val _ = export_theory();

end;
