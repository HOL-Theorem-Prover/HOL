(* ===================================================================== *)
(* FILE          : mk_pair.sml                                           *)
(* DESCRIPTION   : The theory of pairs. This is a mix of the original    *)
(*                 non-definitional theory of pairs from hol88           *)
(*                 and John Harrison's definitional theory of pairs from *)
(*                 GTT.                                                  *)
(*                                                                       *)
(* AUTHOR        : (c) Mike Gordon, John Harrison, Konrad Slind          *)
(*                 Jim Grundy                                            *)
(*                 University of Cambridge                               *)
(* DATE          : August 7, 1997                                        *)
(* ===================================================================== *)

structure pairScript =
struct

open HolKernel Parse basicHol90Lib
     Type_def_support relationTheory mesonLib;

infix THEN THENL |->;

type thm = Thm.thm

val _ = new_theory "pair";

val MK_PAIR_DEF =
 new_definition
      ("MK_PAIR_DEF",
     --`MK_PAIR x y = \a b. (a=x) /\ (b=y)`--);


val IS_PAIR_DEF =
 new_definition
      ("IS_PAIR_DEF",
     --`IS_PAIR P = ?x y. P = MK_PAIR x y`--);

val IS_PAIR_MK_PAIR = prove (
--`!x y. IS_PAIR (MK_PAIR x y)`--,
REWRITE_TAC[IS_PAIR_DEF, MK_PAIR_DEF]
 THEN GEN_TAC THEN GEN_TAC
 THEN EXISTS_TAC(--`x:'a`--) THEN EXISTS_TAC(--`y:'b`--)
 THEN REFL_TAC);

val PAIR_EXISTS = prove(
 --`?P. IS_PAIR P`--,
  REWRITE_TAC[IS_PAIR_DEF]
  THEN MAP_EVERY EXISTS_TAC [--`MK_PAIR p q`--, --`p:'a`--, --`q:'b`--]
  THEN REFL_TAC);


(*---------------------------------------------------------------------------
 * Define the type of pairs.
 *---------------------------------------------------------------------------*)
val prod_TY_DEF = new_type_definition
                    {name = "prod",
                     pred = --`IS_PAIR`--,
                     inhab_thm = PAIR_EXISTS};

val _ = add_infix_type
         {Prec = 70,
          ParseName = SOME "#",
          Name = "prod",
          Assoc = HOLgrammars.RIGHT};

val ABS_REP_prod =
 define_new_type_bijections
  {ABS="ABS_prod",REP="REP_prod", name="ABS_REP_prod", tyax=prod_TY_DEF};


val REP_ABS_PAIR = prove(
 --`!x y. REP_prod (ABS_prod (MK_PAIR x y)) = MK_PAIR x y`--,
 REPEAT GEN_TAC
  THEN MP_TAC (SPEC (--`MK_PAIR x y`--) (CONJUNCT2 ABS_REP_prod))
  THEN REWRITE_TAC[IS_PAIR_MK_PAIR]);


val COMMA_DEF = new_definition (
  "COMMA_DEF",
  --`$, x y = ABS_prod(MK_PAIR x y)`--);

val _ = add_rule {term_name = ",", fixity = Infixr 50,
                  pp_elements = [TOK ",", BreakSpace(0,0)],
                  paren_style = ParoundName,
                  block_style = (AroundSameName, (PP.INCONSISTENT, 0))};

(*---------------------------------------------------------------------------*
 * Projections.                                                              *
 *---------------------------------------------------------------------------*)

val FST_DEF =
 new_definition
      ("FST_DEF",
     --`FST p = @x. ?y. p = (x,y)`--);


val SND_DEF =
 new_definition
      ("SND_DEF",
     --`SND p:'b = @y. ?x. p = (x,y)`--);


val PAIR_EQ = store_thm("PAIR_EQ",
 --`((x,y) = (a,b)) = (x=a) /\ (y=b)`--,
 EQ_TAC THENL
 [REWRITE_TAC[COMMA_DEF]
   THEN DISCH_THEN(MP_TAC o AP_TERM (--`REP_prod`--))
   THEN REWRITE_TAC [REP_ABS_PAIR]
   THEN REWRITE_TAC [MK_PAIR_DEF]
   THEN CONV_TAC (REDEPTH_CONV FUN_EQ_CONV) THEN BETA_TAC
   THEN DISCH_THEN (MP_TAC o SPECL [--`x:'a`--,  --`y:'b`--])
   THEN REWRITE_TAC[],
  STRIP_TAC THEN ASM_REWRITE_TAC[]]);

val CLOSED_PAIR_EQ =
  save_thm("CLOSED_PAIR_EQ", GENL [--`x:'a`--,  --`y:'b`--,
                                   --`a:'a`--,  --`b:'b`--] PAIR_EQ);


val ABS_PAIR_THM = store_thm("ABS_PAIR_THM",
--`!x. ?q r. x = (q,r)`--,
 GEN_TAC THEN REWRITE_TAC[COMMA_DEF]
  THEN MP_TAC(SPEC (--`REP_prod x`--) (CONJUNCT2 ABS_REP_prod))
  THEN REWRITE_TAC[CONJUNCT1 ABS_REP_prod,IS_PAIR_DEF]
  THEN DISCH_THEN(X_CHOOSE_THEN (--`a:'a`--)
                   (X_CHOOSE_THEN(--`b:'b`--) MP_TAC))
  THEN DISCH_THEN(MP_TAC o AP_TERM (--`ABS_prod`--))
  THEN REWRITE_TAC[CONJUNCT1 ABS_REP_prod]
  THEN DISCH_THEN SUBST1_TAC
  THEN MAP_EVERY EXISTS_TAC [--`a:'a`--,  --`b:'b`--]
  THEN REFL_TAC);


(*---------------------------------------------------------------------------
 * Useful rewrite rules.
 *---------------------------------------------------------------------------*)

val FST = store_thm ("FST",   --`!x y. FST(x,y) = x`--,
REPEAT GEN_TAC
 THEN REWRITE_TAC[FST_DEF]
 THEN MATCH_MP_TAC (BETA_RULE
      (SPECL (map Term [`\x'. ?y'. (x,y) = (x',y')`, `x:'a`]) SELECT_UNIQUE))
 THEN GEN_TAC THEN REWRITE_TAC[PAIR_EQ]
 THEN EQ_TAC THEN STRIP_TAC
 THEN ASM_REWRITE_TAC[]
 THEN EXISTS_TAC (--`y:'b`--)
 THEN ASM_REWRITE_TAC[]);


val SND = store_thm ("SND",   --`!x y. SND(x,y) = y`--,
REPEAT GEN_TAC
 THEN REWRITE_TAC[SND_DEF]
 THEN MATCH_MP_TAC (BETA_RULE
        (SPECL [Term`\y':'b. ?x'. (x,y) = (x',y')`, Term`y:'b`]
           (INST_TYPE [Type.alpha |-> Type.beta] SELECT_UNIQUE)))
 THEN GEN_TAC THEN REWRITE_TAC[PAIR_EQ]
 THEN EQ_TAC THEN STRIP_TAC
 THEN ASM_REWRITE_TAC[]
 THEN EXISTS_TAC (--`x:'a`--)
 THEN ASM_REWRITE_TAC[]);


val PAIR = store_thm ("PAIR",   --`!x. (FST x, SND x) = x`--,
GEN_TAC
  THEN STRIP_ASSUME_TAC (SPEC_ALL ABS_PAIR_THM)
   THEN POP_ASSUM SUBST1_TAC
   THEN REWRITE_TAC[FST,SND]);


(*---------------------------------------------------------------------------
 * UNCURRY is needed for terms of the form `\(x,y).t`
 *---------------------------------------------------------------------------*)

val UNCURRY_DEF =
 new_definition
      ("UNCURRY_DEF",
         Term `UNCURRY f (x,y) :'c = f x y`);

val CURRY_DEF =
 new_definition
      ("CURRY_DEF",
         Term`CURRY f x y :'c = f (x,y)`);


val UNCURRY_VAR = store_thm("UNCURRY_VAR",
Term`!f v. UNCURRY f v = f (FST v) (SND v)`,
REPEAT GEN_TAC
 THEN STRIP_ASSUME_TAC (SPEC (Term`v:'a#'b`) ABS_PAIR_THM)
 THEN POP_ASSUM SUBST_ALL_TAC
 THEN REWRITE_TAC[UNCURRY_DEF,FST,SND]);

(* ------------------------------------------------------------------------- *)
(* CURRY_UNCURRY_THM = |- !f. CURRY(UNCURRY f) = f                           *)
(* ------------------------------------------------------------------------- *)

val CURRY_UNCURRY_THM =
    let val th1 = prove
		(--`CURRY (UNCURRY (f:'a->'b->'c)) x y = f x y`--,
		 REWRITE_TAC [UNCURRY_DEF, CURRY_DEF])
	val th2 = GEN (--`y:'b`--) th1
	val th3 = EXT th2
	val th4 = GEN (--`x:'a`--) th3
	val th4 = EXT th4
    in
	GEN (--`f:'a->'b->'c`--) th4
    end;

val _ = save_thm("CURRY_UNCURRY_THM",CURRY_UNCURRY_THM);


(* ------------------------------------------------------------------------- *)
(* UNCURRY_CURRY_THM = |- !f. UNCURRY(CURRY f) = f                           *)
(* ------------------------------------------------------------------------- *)

val UNCURRY_CURRY_THM =
  let val th1 = prove
	(--`UNCURRY (CURRY (f:('a#'b)->'c)) (x,y) = f(x,y)`--,
	 REWRITE_TAC [CURRY_DEF, UNCURRY_DEF])
      val th2 = INST [Term`x:'a` |-> Term`FST (z:'a#'b)`,
		      Term`y:'b` |-> Term`SND (z:'a#'b)`] th1
      val th3 = CONV_RULE (RAND_CONV
                    (RAND_CONV (K (ISPEC(--`z:'a#'b`--) PAIR))))  th2
      val th4 = CONV_RULE(RATOR_CONV (RAND_CONV
                   (RAND_CONV (K (ISPEC(--`z:'a#'b`--) PAIR)))))th3
      val th5 = GEN (--`z:'a#'b`--) th4
      val th6 = EXT th5
  in
	GEN (--`f:('a#'b)->'c`--) th6
  end;

    val _ = save_thm("UNCURRY_CURRY_THM",UNCURRY_CURRY_THM);

(* ------------------------------------------------------------------------- *)
(* CURRY_ONE_ONE_THM = |- (CURRY f = CURRY g) = (f = g)                      *)
(* ------------------------------------------------------------------------- *)
val CURRY_ONE_ONE_THM =
    let val th1 = ASSUME (--`(f:('a#'b)->'c) = g`--)
	val th2 = AP_TERM(--`CURRY:(('a#'b)->'c)->('a->'b->'c)`--) th1
	val th3 = DISCH_ALL th2
	val thA = ASSUME (--`(CURRY (f:('a#'b)->'c)) = (CURRY g)`--)
	val thB = AP_TERM (--`UNCURRY:('a->'b->'c)->(('a#'b)->'c)`--) thA
	val thC = PURE_REWRITE_RULE [UNCURRY_CURRY_THM] thB
	val thD = DISCH_ALL thC
    in
	IMP_ANTISYM_RULE thD th3
    end;

val _ = save_thm("CURRY_ONE_ONE_THM",CURRY_ONE_ONE_THM);

(* ------------------------------------------------------------------------- *)
(* UNCURRY_ONE_ONE_THM = |- (UNCURRY f = UNCURRY g) = (f = g)                *)
(* ------------------------------------------------------------------------- *)

val UNCURRY_ONE_ONE_THM =
    let val th1 = ASSUME (--`(f:'a->'b->'c) = g`--)
	val th2 = AP_TERM (--`UNCURRY:('a->'b->'c)->(('a#'b)->'c)`--) th1
	val th3 = DISCH_ALL th2
	val thA = ASSUME (--`(UNCURRY (f:'a->'b->'c)) = (UNCURRY g)`--)
	val thB = AP_TERM (--`CURRY:(('a#'b)->'c)->('a->'b->'c)`--) thA
	val thC = PURE_REWRITE_RULE [CURRY_UNCURRY_THM] thB
	val thD = DISCH_ALL thC
    in
	IMP_ANTISYM_RULE thD th3
    end;

val _ = save_thm("UNCURRY_ONE_ONE_THM",UNCURRY_ONE_ONE_THM);


val EXISTS_PROD = store_thm("EXISTS_PROD",
 Term`(?p. P p) = (?p_1 p_2. P (p_1,p_2))`,
 EQ_TAC THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [Term`FST (p:'a # 'b)`, Term`SND (p:'a # 'b)`],
      EXISTS_TAC (Term`p_1, p_2`)]
 THEN ASM_REWRITE_TAC[PAIR]);


val FORALL_PROD = store_thm("FORALL_PROD",
 Term`(!p. P p) = (!p_1 p_2. P (p_1,p_2))`,
 EQ_TAC THENL
 [DISCH_THEN(fn th =>
     REPEAT GEN_TAC THEN ASSUME_TAC (SPEC (Term`p_1, p_2`) th)),
  REPEAT STRIP_TAC
    THEN REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC
        (SPEC (Term`p:'a#'b`) ABS_PAIR_THM)]
 THEN ASM_REWRITE_TAC[]);

val pair_induction =
 save_thm("pair_induction",
          #2(EQ_IMP_RULE FORALL_PROD));

(* ------------------------------------------------------------------------- *)
(* PFORALL_THM = |- !P. (!x y. P x y) = (!(x,y). P x y)                      *)
(* ------------------------------------------------------------------------- *)

val PFORALL_THM =
 prove
 (--`!P. (!(x:'a) (y:'b). P x y) = !(x,y):'a#'b. P x y`--,
 GEN_TAC THEN EQ_TAC THENL
 [ DISCH_TAC THEN
   REWRITE_TAC [FORALL_DEF] THEN BETA_TAC THEN ASM_REWRITE_TAC []
   THEN CONV_TAC FUN_EQ_CONV THEN GEN_TAC THEN BETA_TAC
   THEN MP_TAC (SPEC(Term`p:'a#'b`) ABS_PAIR_THM) THEN STRIP_TAC
   THEN ASM_REWRITE_TAC [UNCURRY_DEF],

   DISCH_THEN (fn th => REPEAT GEN_TAC THEN
     MP_TAC (SPEC (Term`(x,y): 'a#'b`)
             (BETA_RULE (CONV_RULE FUN_EQ_CONV
              (BETA_RULE (REWRITE_RULE [FORALL_DEF] th))))))
   THEN REWRITE_TAC[UNCURRY_DEF] THEN BETA_TAC THEN STRIP_TAC]);

val _ = save_thm("PFORALL_THM",PFORALL_THM);

(* ------------------------------------------------------------------------- *)
(* PEXISTS_THM = |- !P. (?x y. P x y) = (?(x,y). P x y)                      *)
(* ------------------------------------------------------------------------- *)

val PEXISTS_THM = prove
(--`!P. (?(x:'a) (y:'b). P x y) = ?(x,y):'a#'b. P x y`--,
GEN_TAC THEN EQ_TAC THENL
 [STRIP_TAC THEN ASM_REWRITE_TAC[EXISTS_DEF] THEN BETA_TAC
  THEN REWRITE_TAC[UNCURRY_VAR] THEN BETA_TAC THEN
  SUBGOAL_THEN(Term`?v:'a#'b. UNCURRY (\x y. P x y) v`) MP_TAC THENL
  [EXISTS_TAC(Term`x,y`) THEN REWRITE_TAC[UNCURRY_DEF] THEN BETA_TAC
   THEN ASM_REWRITE_TAC[],
   STRIP_TAC THEN IMP_RES_TAC SELECT_AX
   THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM MP_TAC
   THEN REWRITE_TAC[UNCURRY_VAR] THEN BETA_TAC THEN STRIP_TAC],
  DISCH_THEN (fn th => MP_TAC(BETA_RULE(REWRITE_RULE[EXISTS_DEF]th)))
   THEN REWRITE_TAC[UNCURRY_VAR] THEN BETA_TAC THEN DISCH_TAC
   THEN EXISTS_TAC (Term`FST (@(x,y):'a#'b. P x y)`)
   THEN EXISTS_TAC (Term`SND (@(x,y):'a#'b. P x y)`)
   THEN ASM_REWRITE_TAC[]]);

val _ = save_thm("PEXISTS_THM",PEXISTS_THM);


val pair_Axiom = store_thm("pair_Axiom",
  --`!f:'a->'b->'c. ?fn. !x y. fn (x,y) = f x y`--,
  GEN_TAC THEN EXISTS_TAC(--`UNCURRY f :'a#'b ->'c`--) THEN
  REWRITE_TAC[UNCURRY_DEF]);

val UNCURRY_CONG =
  save_thm("UNCURRY_CONG", Prim_rec.case_cong_thm ABS_PAIR_THM UNCURRY_DEF);

(*---------------------------------------------------------------------------
    For TFL support.
 ---------------------------------------------------------------------------*)

val pair_case_def =
  new_definition("pair_case_def", Term`pair_case = UNCURRY`);

val pair_case_thm = save_thm("pair_case_thm",
   Rewrite.REWRITE_RULE [UNCURRY_DEF]
      (MK_COMB(MK_COMB (pair_case_def, REFL(Term`f:'a->'b ->'c`)),
               REFL (Term`(x,y)`))));

val pair_case_cong = save_thm("pair_case_cong",
 Rewrite.PURE_REWRITE_RULE[GSYM pair_case_def] UNCURRY_CONG);

val pair_rws = [PAIR, FST, SND];

(* pair_rws formerly also had

    CLOSED_PAIR_EQ,
    CURRY_UNCURRY_THM, UNCURRY_CURRY_THM,
    CURRY_ONE_ONE_THM, UNCURRY_ONE_ONE_THM];

  but they weren't getting used.
*)


(*---------------------------------------------------------------------------
    Generate some ML that gets evaluated at theory load time.

    The TFL definition package uses "pair_case" as a case construct,
    rather than UNCURRY. This (apparently) solves a deeply buried
    problem in termination condition extraction involving paired
    beta-reduction.

 ---------------------------------------------------------------------------*)

val _ = adjoin_to_theory
{sig_ps = SOME(fn ppstrm => PP.add_string ppstrm "val pair_rws : thm list"),
 struct_ps = SOME(fn ppstrm =>
   let val S = PP.add_string ppstrm
       fun NL() = PP.add_newline ppstrm
   in
      S "val pair_rws = [PAIR, FST, SND];";   NL();
      S "val _ = TypeBase.write";             NL();
      S "  (TypeBase.mk_tyinfo";              NL();
      S "     {ax=pair_Axiom,";               NL();
      S "      case_def=pair_case_thm,";      NL();
      S "      case_cong=pair_case_cong,";    NL();
      S "      induction=pair_induction,";    NL();
      S "      nchotomy=ABS_PAIR_THM,";       NL();
      S "      size=NONE,";                   NL();
      S "      one_one=SOME CLOSED_PAIR_EQ,"; NL();
      S "      distinct=NONE});"
  end)};


(*---------------------------------------------------------------------------
                 Wellfoundedness and pairs.
 ---------------------------------------------------------------------------*)


(*---------------------------------------------------------------------------
 * The lexicographic combination of two wellfounded orderings is wellfounded.
 * The minimal element of this relation is found by
 *
 *    1. Finding the set of first elements of the pairs in B
 *    2. That set is non-empty, so it has an R-minimal element, call it min
 *    3. Find the set of second elements of those pairs in B whose first
 *       element is min.
 *    4. This set is non-empty, so it has a Q-minimal element, call it min'.
 *    5. A minimal element is (min,min').
 *---------------------------------------------------------------------------*)

val LEX_DEF =
Q.new_infixr_definition
("LEX_DEF",
  `$LEX (R1:'a->'a->bool) (R2:'b->'b->bool)
     =
   \(s,t) (u,v). R1 s u \/ (s=u) /\ R2 t v`, 450);

val WF_LEX = Q.store_thm("WF_LEX",
 `!(R:'a->'a->bool) (Q:'b->'b->bool). WF R /\ WF Q ==> WF (R LEX Q)`,
REWRITE_TAC [LEX_DEF, relationTheory.WF_DEF]
  THEN CONV_TAC (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
  THEN REPEAT STRIP_TAC
  THEN Q.SUBGOAL_THEN `?w1. (\v. ?y. B (v,y)) w1`  STRIP_ASSUME_TAC THENL
  [BETA_TAC THEN MAP_EVERY Q.EXISTS_TAC [`FST w`, `SND w`]
     THEN ASM_REWRITE_TAC pair_rws,
   Q.SUBGOAL_THEN
   `?min. (\v. ?y. B (v,y)) min
         /\ !b. R b min ==>
               ~(\v. ?y. B (v,y)) b` STRIP_ASSUME_TAC THENL
   [RES_TAC THEN ASM_MESON_TAC[],
    Q.SUBGOAL_THEN
      `?w2:'b. (\z. B (min:'a,z)) w2` STRIP_ASSUME_TAC THENL
    [BETA_TAC THEN RULE_ASSUM_TAC BETA_RULE THEN ASM_REWRITE_TAC[],
     Q.SUBGOAL_THEN
     `?min':'b. (\z. B (min,z)) min'
       /\  !b. Q b min' ==>
              ~((\z. B (min,z)) b)` STRIP_ASSUME_TAC THENL
     [RES_TAC THEN ASM_MESON_TAC[],
      RULE_ASSUM_TAC BETA_RULE
       THEN EXISTS_TAC (Term`(min:'a, (min':'b))`)
       THEN ASM_REWRITE_TAC[]
       THEN GEN_TAC THEN SUBST_TAC [GSYM(Q.SPEC`b:'a#'b` PAIR)]
       THEN REWRITE_TAC [UNCURRY_DEF] THEN BETA_TAC
       THEN REWRITE_TAC [UNCURRY_DEF] THEN BETA_TAC
       THEN ASM_MESON_TAC pair_rws]]]]);

(*---------------------------------------------------------------------------
 * The relational product of two wellfounded relations is wellfounded. This
 * is a consequence of WF_X.
 *---------------------------------------------------------------------------*)

val RPROD_DEF =
Q.new_definition
("RPROD_DEF",
   `RPROD (R1:'a->'a->bool)
          (R2:'b->'b->bool) = \(s,t) (u,v). R1 s u /\ R2 t v`);


val WF_RPROD =
Q.store_thm("WF_RPROD",
 `!(R:'a->'a->bool) (Q:'b->'b->bool). WF R /\ WF Q  ==>  WF(RPROD R Q)`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC relationTheory.WF_SUBSET
 THEN Q.EXISTS_TAC`R LEX Q`
 THEN CONJ_TAC
 THENL [MATCH_MP_TAC WF_LEX THEN ASM_REWRITE_TAC[],
        REWRITE_TAC[LEX_DEF,RPROD_DEF]
         THEN GEN_TAC THEN SUBST_TAC [GSYM(Q.SPEC`x:'a#'b` PAIR)]
         THEN GEN_TAC THEN SUBST_TAC [GSYM(Q.SPEC`y:'a#'b` PAIR)]
         THEN REWRITE_TAC [UNCURRY_DEF] THEN BETA_TAC
         THEN REWRITE_TAC [UNCURRY_DEF] THEN BETA_TAC
         THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);


(*---------------------------------------------------------------------------
        Distribution laws for paired lets. Only will work for the
        exact form!
 ---------------------------------------------------------------------------*)

val LET2_RAND = store_thm("LET2_RAND",
Term`!(P:'c->'d) (M:'a#'b) N.
    P (let (x,y) = M in N x y) = (let (x,y) = M in P (N x y))`,
REWRITE_TAC[boolTheory.LET_DEF] THEN REPEAT GEN_TAC THEN BETA_TAC
 THEN REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC
       (SPEC (Term `M:'a#'b`) ABS_PAIR_THM)
 THEN REWRITE_TAC[UNCURRY_DEF] THEN BETA_TAC THEN REFL_TAC);

val LET2_RATOR = store_thm("LET2_RATOR",
Term`!(M:'a1#'a2) (N:'a1->'a2->'b->'c) (b:'b).
      (let (x,y) = M in N x y) b = let (x,y) = M in N x y b`,
REWRITE_TAC [boolTheory.LET_DEF] THEN BETA_TAC
  THEN REWRITE_TAC [UNCURRY_VAR] THEN BETA_TAC
  THEN REWRITE_TAC[]);

val _ = export_theory();
val _ =
  export_theory_as_docfiles (Path.concat (Path.parentArc, "help/thms"))
end;
