(* ===================================================================== *)
(* FILE          : mk_bool.sml                                           *)
(* DESCRIPTION   : Definition of the logical constants and assertion of  *)
(*                 the axioms.                                           *)
(* AUTHOR        : (c) Mike Gordon, University of Cambridge              *)
(* ===================================================================== *)

structure boolScript =
struct

local open minTheory in end;

open HolKernel Parse;

type thm = Thm.thm;

val _ = new_theory "bool";


(*---------------------------------------------------------------------------*
 *                   DEFINITIONS                                             *
 *---------------------------------------------------------------------------*)

val EXISTS_DEF = define_exists();  (* Grandfather *)
val _ = add_binder ("?", term_grammar.std_binder_precedence)

val TOK = term_grammar.TOK
val TM = term_grammar.TM

val T_DEF =
 new_definition
   ("T_DEF", Term `T = ((\x:bool. x) = \x:bool. x)`);

val FORALL_DEF =
 new_binder_definition
   ("FORALL_DEF", Term `! = \P:'a->bool. P = \x. T`);

val new_infix_definition = Parse.new_infixr_definition

val AND_DEF =
 new_infix_definition
   ("AND_DEF",  Term `/\ = \t1. \t2. !t. (t1 ==> (t2 ==> t)) ==> t`, 400);

val OR_DEF =
 new_infix_definition
   ("OR_DEF", Term `\/ = \t1 t2. !t. (t1 ==> t) ==> ((t2 ==> t) ==> t)`, 300);

val F_DEF =
 new_definition
   ("F_DEF", Term `F = !t. t`);

val NOT_DEF = new_gen_definition ("NOT_DEF", Term `~ = \t. t ==> F`,
                                  TruePrefix 900);

val EXISTS_UNIQUE_DEF =
 new_binder_definition
   ("EXISTS_UNIQUE_DEF",
     Term `?! = \P:'a->bool. ($? P) /\ !x y. (P x /\ P y) ==> (x=y)`);

val LET_DEF =
 new_definition ("LET_DEF",  Term `LET = \(f:'a->'b) (x:'a). f x`);
(* the magic in Parse, will turn the "let" term produced into one that
   actually uses "LET", similarly for and *)
val _ = add_rule ("let", TruePrefix 10, [TOK "let", TM, TOK "in"]);
val _ = add_infix ("and", 9, HOLgrammars.LEFT)

val COND_DEF =
 new_definition
   ("COND_DEF", Term `COND = \t t1 t2. @x:'a. ((t=T) ==> (x=t1)) /\
                                              ((t=F) ==> (x=t2))`);
val _ = add_rule("COND", Infix (HOLgrammars.RIGHT, 11),
                 [TOK "=>", TM, TOK "|"]);
val _ = add_rule("COND", TruePrefix 70,
                 [TOK "if", TM, TOK "then", TM, TOK "else"]);

val ONE_ONE_DEF =
 new_definition
   ("ONE_ONE_DEF",
      Term `ONE_ONE (f:'a->'b) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`);

val ONTO_DEF =
 new_definition
   ("ONTO_DEF", Term `ONTO (f:'a->'b) = !y.?x. y = f x`);

val TYPE_DEFINITION =
 new_definition
   ("TYPE_DEFINITION",
      Term `!P rep. TYPE_DEFINITION (P:'a->bool) (rep:'b->'a)
                    =
                     (!x' x''. (rep x' = rep x'') ==> (x' = x'')) /\
                     (!x. P x = (?x'. x = rep x'))`);


(*---------------------------------------------------------------------------*
 *                   AXIOMS                                                  *
 *---------------------------------------------------------------------------*)

val BOOL_CASES_AX =
 new_axiom
   ("BOOL_CASES_AX", Term `!t:bool. (t=T) \/ (t=F)`);

val IMP_ANTISYM_AX =
 new_axiom
   ("IMP_ANTISYM_AX", Term`!t1 t2. (t1 ==> t2) ==> (t2 ==> t1) ==> (t1 = t2)`);

val ETA_AX =
 new_axiom
   ("ETA_AX", Term `!t:'a->'b. (\x. t x) = t`);

val SELECT_AX =
 new_axiom
   ("SELECT_AX", Term `!(P:'a->bool) x. P x ==> P ($@ P)`);

val INFINITY_AX =
 new_axiom
   ("INFINITY_AX",  Term `?f:ind->ind. ONE_ONE f /\ ~ONTO f`);



(*---------------------------------------------------------------------------*
 * Miscellaneous utility definitions, of use in some automated tools.        *
 *---------------------------------------------------------------------------*)
val ARB_DEF =
 new_definition
   ("ARB_DEF",  Term `ARB = @x:'a. T`);

val bool_case_DEF =
 new_definition
   ("bool_case_DEF",  Term`bool_case (x:'a) y b = COND b x y`);


(*---------------------------------------------------------------------------*
 *                   THEOREMS                                                *
 *---------------------------------------------------------------------------*)

val --> = Type.-->
infix ## |->;
infixr -->;

fun EXT th =
   let val {Bvar,...} = dest_forall(concl th)
       val th1 = SPEC Bvar th
       val {lhs=t1x, rhs=t2x} = dest_eq(concl th1)
       val x = #Rand(dest_comb t1x)
       val th2 = ABS x th1
   in
   TRANS (TRANS(SYM(ETA_CONV (mk_abs{Bvar=x, Body=t1x}))) th2)
         (ETA_CONV (mk_abs{Bvar=x,Body=t2x}))
   end;
fun DISCH_ALL th = DISCH_ALL (DISCH (hd (hyp th)) th) handle _ => th;

fun DISJ_CASES_UNION dth ath bth =
    DISJ_CASES dth (DISJ1 ath (concl bth)) (DISJ2 (concl ath) bth);

fun PROVE_HYP ath bth =  MP (DISCH (concl ath) bth) ath;

fun CONV_RULE conv th = EQ_MP (conv(concl th)) th;
fun RAND_CONV conv tm =
   let val {Rator,Rand} = dest_comb tm
   in AP_TERM Rator (conv Rand)
   end;
fun RATOR_CONV conv tm =
   let val {Rator,Rand} = dest_comb tm
   in AP_THM (conv Rator) Rand
   end;
fun RIGHT_BETA th = TRANS th (BETA_CONV(#rhs(dest_eq(concl th))));
fun UNDISCH th = MP th (ASSUME(#ant(dest_imp(concl th))));
fun CONJ_PAIR thm = (CONJUNCT1 thm, CONJUNCT2 thm);
fun GENL varl thm = itlist GEN varl thm;
fun SPECL tm_list th = rev_itlist SPEC tm_list th
fun IMP_ANTISYM_RULE th1 th2 =
    let val {ant,conseq} = dest_imp(concl th1)
    in
      MP (MP (SPEC conseq (SPEC ant IMP_ANTISYM_AX)) th1) th2
    end

(*---------------------------------------------------------------------------
 * |- !t. F ==> t
 *---------------------------------------------------------------------------*)
val FALSITY =
   let val t = --`t:bool`--
   in
    GEN t (DISCH (--`F`--)
                 (SPEC t (EQ_MP F_DEF (ASSUME (--`F`--)))))
   end;

val _ = save_thm("FALSITY", FALSITY);

fun CONTR tm th = MP (SPEC tm FALSITY) th

fun DISJ_IMP dth =
   let val {disj1,disj2} = dest_disj (concl dth)
       val nota = mk_neg disj1
   in
     DISCH nota
      (DISJ_CASES dth
         (CONTR disj2 (MP (ASSUME nota) (ASSUME disj1)))
         (ASSUME disj2))
   end

fun EQF_INTRO th = IMP_ANTISYM_RULE (NOT_ELIM th)
        (DISCH (Term`F`) (CONTR (dest_neg (concl th)) (ASSUME (Term`F`))));

fun SELECT_EQ x =
 let val ty = type_of x
     val choose = mk_const{Name="@", Ty=(ty --> Type.bool) --> ty}
 in
  fn th => AP_TERM choose (ABS x th)
 end

fun GEN_ALL th = itlist GEN (set_diff (free_vars(concl th))
                                      (free_varsl (hyp th))) th;

local fun f v (vs,l) = let val v' = variant vs v in (v'::vs, v'::l) end
in
fun SPEC_ALL th =
   let val (hvs,con) = (free_varsl ## I) (hyp th, concl th)
       val fvs = free_vars con
       and vars = fst(strip_forall con)
   in
     SPECL (snd(itlist f vars (hvs@fvs,[]))) th
   end
end;

fun CONJUNCTS th =
  (CONJUNCTS (CONJUNCT1 th) @ CONJUNCTS (CONJUNCT2 th)) handle _ => [th];

fun SUBST_CONV theta template tm =
  let fun retheta {redex,residue} = (redex |-> genvar(type_of redex))
      val theta0 = map retheta theta
      val theta1 = map2 (curry (op |->))
                        (map #residue theta0) (map #residue theta)
  in
   SUBST theta1 (mk_eq{lhs=tm,rhs=subst theta0 template}) (REFL tm)
  end;

fun IMP_TRANS th1 th2 =
   let val {ant,conseq} = dest_imp(concl th1)
   in DISCH ant (MP th2 (MP th1 (ASSUME ant))) end;

fun ADD_ASSUM t th = MP (DISCH t th) (ASSUME t);

fun SPEC_VAR th =
   let val {Bvar,...} = dest_forall (concl th)
       val bv' = variant (free_varsl (hyp th)) Bvar
   in (bv', SPEC bv' th)
   end;

 fun MK_EXISTS bodyth =
    let val (x, sth) = SPEC_VAR bodyth
        val {lhs=a, rhs=b} = dest_eq (concl sth)
        val (abimp,baimp) = EQ_IMP_RULE sth
        fun HALF (p,q) pqimp =
           let val xp = mk_exists{Bvar=x,Body=p}
               and xq = mk_exists{Bvar=x,Body=q}
           in DISCH xp
               (CHOOSE (x, ASSUME xp) (EXISTS (xq,x) (MP pqimp (ASSUME p))))
           end
    in
      IMP_ANTISYM_RULE (HALF (a,b) abimp) (HALF (b,a) baimp)
    end;

fun SELECT_RULE th =
  let val (tm as {Bvar, Body}) = dest_exists(concl th)
      val v = genvar(type_of Bvar)
      val P = mk_abs tm
      val alpha = mk_vartype"'a"
      val SELECT_AX' = INST_TYPE[alpha |-> type_of Bvar] SELECT_AX
      val th1 = SPEC v (SPEC P SELECT_AX')
      val {ant,conseq} = dest_imp(concl th1)
      val th2 = BETA_CONV ant
      and th3 = BETA_CONV conseq
      val th4 = EQ_MP th3 (MP th1 (EQ_MP(SYM th2) (ASSUME (rhs(concl th2)))))
  in
     CHOOSE (v,th) th4
  end;


val ETA_THM = GEN_ALL(ETA_CONV (Term`\x:'a. (M x:'b)`));
val _ = save_thm("ETA_THM",ETA_THM);

(*---------------------------------------------------------------------------
 *  |- T
 *---------------------------------------------------------------------------*)
val TRUTH = EQ_MP (SYM T_DEF) (REFL (--`\x:bool. x`--));
val _ = save_thm("TRUTH",TRUTH);

fun EQT_ELIM th = EQ_MP (SYM th) TRUTH;

fun EQT_INTRO th =
   let val t = concl th
   in
     MP (MP (SPEC (Term`T`) (SPEC t IMP_ANTISYM_AX))
            (DISCH t TRUTH))
        (DISCH (Term`T`) th)
   end;


(*---------------------------------------------------------------------------
 *  |- !t. t \/ ~t
 *---------------------------------------------------------------------------*)
val EXCLUDED_MIDDLE =
   let val t = --`t:bool`--
       val th1 = RIGHT_BETA(AP_THM NOT_DEF t)
       val th2 = DISJ1 (EQT_ELIM(ASSUME (--`^t = T`--))) (--`~ ^t`--)
       and th3 = DISJ2 t (EQ_MP (SYM th1)
                                (DISCH t (EQ_MP (ASSUME (--`^t = F`--))
                                                (ASSUME t))))
   in
      GEN t (DISJ_CASES (SPEC t BOOL_CASES_AX) th2 th3)
   end;

val _ = save_thm("EXCLUDED_MIDDLE",EXCLUDED_MIDDLE);

fun IMP_ELIM th =
  let val {ant,conseq} = dest_imp (concl th)
       val not_t1 = mk_neg ant
  in
   DISJ_CASES (SPEC ant EXCLUDED_MIDDLE)
              (DISJ2 not_t1 (MP th (ASSUME ant)))
              (DISJ1 (ASSUME not_t1) conseq)
  end;

(*---------------------------------------------------------------------------*
 *  |- !f y. (\x. f x) y = f y                                               *
 *---------------------------------------------------------------------------*)
val BETA_THM =
   GENL [Term`f:'a->'b`, Term `y:'a`]
        (BETA_CONV (Term`(\x. (f:'a->'b) x) y`));

val _ = save_thm("BETA_THM", BETA_THM);

(*---------------------------------------------------------------------------*
 *  |- !t1:'a. !t2:'b. (\x. t1) t2 = t1                                      *
 *---------------------------------------------------------------------------*)
val ABS_SIMP =
   GENL [Term`t1:'a`, Term `t2:'b`]
        (BETA_CONV (Term`(\x:'b. t1:'a) t2`));

val _ = save_thm("ABS_SIMP", ABS_SIMP);

(*---------------------------------------------------------------------------
 *   |- !t. (!x.t)  =  t
 *---------------------------------------------------------------------------*)
val FORALL_SIMP =
 let val t = --`t:bool`--
     val x = --`x:'a`--
 in
 GEN t (IMP_ANTISYM_RULE
        (DISCH (--`!^x.^t`--) (SPEC x (ASSUME (--`!^x.^t`--))))
        (DISCH t (GEN x (ASSUME t))))
 end;

val _ = save_thm("FORALL_SIMP", FORALL_SIMP);

(*---------------------------------------------------------------------------
 *   |- !t. (?x.t)  =  t
 *---------------------------------------------------------------------------*)
val EXISTS_SIMP =
   let val t = --`t:bool`--
       and x = --`x:'a`--
       val ext = --`?^x.^t`--
   in
   GEN t (IMP_ANTISYM_RULE
           (DISCH ext (CHOOSE((--`p:'a`--), ASSUME ext) (ASSUME t)))
           (DISCH t (EXISTS(ext, --`r:'a`--) (ASSUME t))))
   end;

val _ = save_thm("EXISTS_SIMP", EXISTS_SIMP);


(*---------------------------------------------------------------------------
 *       |- !t1 t2. t1 ==> t2 ==> t1 /\ t2
 *---------------------------------------------------------------------------*)
val AND_INTRO_THM =
   let val t = --`t:bool`--
       and t1 = --`t1:bool`--
       and t2 = --`t2:bool`--
       val t12 = --`^t1 ==> (^t2 ==> ^t)`--
       val th1 = GEN t (DISCH t12 (MP (MP (ASSUME t12)
                                          (ASSUME t1))
                                      (ASSUME t2)))
       val th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM AND_DEF t1)) t2)
   in
   GEN t1 (GEN t2 (DISCH t1 (DISCH t2 (EQ_MP (SYM th2) th1))))
   end;

val _ = save_thm("AND_INTRO_THM", AND_INTRO_THM);

(*---------------------------------------------------------------------------
 * |- !t1 t2. t1 /\ t2 ==> t1
 *---------------------------------------------------------------------------*)
val AND1_THM =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ASSUME (--`^t1 /\ ^t2`--)
      val th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM AND_DEF t1)) t2)
      val th3 = SPEC t1 (EQ_MP th2 th1)
      val th4 = DISCH t1 (DISCH t2 (ADD_ASSUM t2 (ASSUME t1)))
  in
  GEN t1 (GEN t2 (DISCH (--`^t1 /\ ^t2`--) (MP th3 th4)))
  end;

val _ = save_thm("AND1_THM", AND1_THM);


(*---------------------------------------------------------------------------
 *    |- !t1 t2. t1 /\ t2 ==> t2
 *---------------------------------------------------------------------------*)
val AND2_THM =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ASSUME (--`^t1 /\ ^t2`--)
      val th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM AND_DEF t1)) t2)
      val th3 = SPEC t2 (EQ_MP th2 th1)
      val th4 = DISCH t1 (DISCH t2 (ADD_ASSUM t1 (ASSUME t2)))
  in
  GEN t1 (GEN t2 (DISCH (--`^t1 /\ ^t2`--) (MP th3 th4)))
  end;

val _ = save_thm("AND2_THM", AND2_THM);

(*---------------------------------------------------------------------------
 *   |- !t1 t2. (t1 /\ t2) = (t2 /\ t1)
 *---------------------------------------------------------------------------*)
val CONJ_SYM =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ASSUME (--`^t1 /\ ^t2`--)
      and th2 = ASSUME (--`^t2 /\ ^t1`--)
  in
  GEN t1 (GEN t2 (IMP_ANTISYM_RULE
                 (DISCH (--`^t1 /\ ^t2`--)
                        (CONJ(CONJUNCT2 th1)(CONJUNCT1 th1)))
                 (DISCH (--`^t2 /\ ^t1`--)
                        (CONJ(CONJUNCT2 th2)(CONJUNCT1 th2)))))
  end;

val _ = save_thm("CONJ_SYM", CONJ_SYM);
val _ = save_thm("CONJ_COMM", CONJ_SYM);

(*---------------------------------------------------------------------------
 * |- !t1 t2 t3. t1 /\ (t2 /\ t3) = (t1 /\ t2) /\ t3
 *---------------------------------------------------------------------------*)
val CONJ_ASSOC =
  let val t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      and t3 = --`t3:bool`--
      val th1 = ASSUME (--`^t1 /\ (^t2 /\ ^t3)`--)
      val th2 = ASSUME (--`(^t1 /\ ^t2) /\ ^t3`--)
      val th3 = DISCH (--`^t1 /\ (^t2 /\ ^t3)`--)
                   (CONJ (CONJ(CONJUNCT1 th1)
                              (CONJUNCT1(CONJUNCT2 th1)))
                         (CONJUNCT2(CONJUNCT2 th1)))
      and th4 = DISCH (--`(^t1 /\ ^t2) /\ ^t3`--)
                   (CONJ (CONJUNCT1(CONJUNCT1 th2))
                         (CONJ(CONJUNCT2(CONJUNCT1 th2))
                              (CONJUNCT2 th2)))
  in
  GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE th3 th4)))
  end;

val _ = save_thm("CONJ_ASSOC", CONJ_ASSOC);


(*---------------------------------------------------------------------------
 *  |- !t1 t2. t1 ==> t1 \/ t2
 *---------------------------------------------------------------------------*)
val OR_INTRO_THM1 =
  let val t = --`t:bool`--
      and t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ADD_ASSUM (--`^t2 ==> ^t`--) (MP (ASSUME (--`^t1 ==> ^t`--))
                                              (ASSUME t1))
      val th2 = GEN t (DISCH (--`^t1 ==> ^t`--) (DISCH (--`^t2 ==> ^t`--) th1))
      val th3 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM OR_DEF t1)) t2)
  in
    GEN t1 (GEN t2 (DISCH t1 (EQ_MP (SYM th3) th2)))
  end;

val _ = save_thm("OR_INTRO_THM1", OR_INTRO_THM1);

(*---------------------------------------------------------------------------
 * |- !t1 t2. t2 ==> t1 \/ t2
 *---------------------------------------------------------------------------*)
val OR_INTRO_THM2 =
  let val t  = --`t:bool`--
      and t1 = --`t1:bool`--
      and t2 = --`t2:bool`--
      val th1 = ADD_ASSUM (--`^t1 ==> ^t`--)
                     (MP (ASSUME (--`^t2 ==> ^t`--)) (ASSUME t2))
      val th2 = GEN t (DISCH (--`^t1 ==> ^t`--) (DISCH (--`^t2 ==> ^t`--) th1))
      val th3 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM OR_DEF t1)) t2)
  in
    GEN t1 (GEN t2 (DISCH t2 (EQ_MP (SYM th3) th2)))
  end;

val _ = save_thm("OR_INTRO_THM2", OR_INTRO_THM2);

(*---------------------------------------------------------------------------
 * |- !t t1 t2. (t1 \/ t2) ==> (t1 ==> t) ==> (t2 ==> t) ==> t
 *---------------------------------------------------------------------------*)
val OR_ELIM_THM =
   let val t =  --`t:bool`--
       and t1 = --`t1:bool`--
       and t2 = --`t2:bool`--
       val th1 = ASSUME (--`^t1 \/ ^t2`--)
       and th2 = RIGHT_BETA(AP_THM (RIGHT_BETA(AP_THM OR_DEF t1)) t2)
       val th3 = SPEC t (EQ_MP th2 th1)
       val th4 = MP (MP th3 (ASSUME (--`^t1 ==> ^t`--)))
                    (ASSUME (--`^t2 ==> ^t`--))
       val th4 = DISCH (--`^t1 ==> ^t`--) (DISCH (--`^t2 ==> ^t`--) th4)
   in
   GEN t (GEN t1 (GEN t2 (DISCH (--`^t1 \/ ^t2`--) th4)))
   end;

val _ = save_thm("OR_ELIM_THM", OR_ELIM_THM);


(*---------------------------------------------------------------------------
 * |- !t. (t ==> F) ==> ~t
 *---------------------------------------------------------------------------*)
val IMP_F =
   let val t = --`t:bool`--
       val th1 = RIGHT_BETA (AP_THM NOT_DEF t)
   in
     GEN t (DISCH (--`^t ==> F`--)
                 (EQ_MP (SYM th1) (ASSUME (--`^t ==> F`--))))
   end;

val _ = save_thm("IMP_F", IMP_F);


(*---------------------------------------------------------------------------
 * |- !t. ~t ==> (t ==> F)
 *---------------------------------------------------------------------------*)
val F_IMP =
   let val t = --`t:bool`--
       val th1 = RIGHT_BETA(AP_THM NOT_DEF t)
   in
   GEN t (DISCH (--`~^t`--)
                (EQ_MP th1 (ASSUME (--`~^t`--))))
   end;

val _ = save_thm("F_IMP", F_IMP);


(*---------------------------------------------------------------------------
 * |- !t. ~t ==> (t=F)
 *---------------------------------------------------------------------------*)
val NOT_F =
   let val t = --`t:bool`--
       val th1 = MP (SPEC t F_IMP) (ASSUME (--`~ ^t`--))
       and th2 = SPEC t FALSITY
       and th3 = SPEC (--`F`--) (SPEC t IMP_ANTISYM_AX)
   in
   GEN t (DISCH (--`~^t`--) (MP (MP th3 th1) th2))
   end;

val _ = save_thm("NOT_F", NOT_F);

(*---------------------------------------------------------------------------
 *  |- !t. ~(t /\ ~t)
 *---------------------------------------------------------------------------*)

val NOT_AND =
   let val th = ASSUME (--`t /\ ~t`--)
   in NOT_INTRO(DISCH (--`t /\ ~t`--) (MP (CONJUNCT2 th) (CONJUNCT1 th)))
   end;

val _ = save_thm("NOT_AND", NOT_AND);


(*---------------------------------------------------------------------------
 * |- !t. (T /\ t) = t
 *---------------------------------------------------------------------------*)
val AND_CLAUSE1 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`T /\ ^t`--) (CONJUNCT2(ASSUME (--`T /\ ^t`--)))
       and th2 = DISCH t (CONJ TRUTH (ASSUME t))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t. (t /\ T) = t
 *---------------------------------------------------------------------------*)
val AND_CLAUSE2 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t /\ T`--) (CONJUNCT1(ASSUME (--`^t /\ T`--)))
       and th2 = DISCH t (CONJ (ASSUME t) TRUTH)
   in
     GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *   |- !t. (F /\ t) = F
 *---------------------------------------------------------------------------*)
val AND_CLAUSE3 =
   let val t = --`t:bool`--
       val th1 = IMP_TRANS (SPEC t (SPEC (--`F`--) AND1_THM))
                           (SPEC (--`F`--) FALSITY)
       and th2 = SPEC (--`F /\ ^t`--) FALSITY
   in
     GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *   |- !t. (t /\ F) = F
 *---------------------------------------------------------------------------*)
val AND_CLAUSE4 =
   let val t = --`t:bool`--
       val th1 = IMP_TRANS (SPEC (--`F`--) (SPEC t AND2_THM))
                           (SPEC (--`F`--) FALSITY)
       and th2 = SPEC (--`^t /\ F`--) FALSITY
   in
     GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *    |- !t. (t /\ t) = t
 *---------------------------------------------------------------------------*)
val AND_CLAUSE5 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t /\ ^t`--) (CONJUNCT1(ASSUME (--`^t /\ ^t`--)))
       and th2 = DISCH t (CONJ(ASSUME t)(ASSUME t))
   in
     GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (T /\ t) = t /\
 *         (t /\ T) = t /\
 *         (F /\ t) = F /\
 *         (t /\ F) = F /\
 *         (t /\ t) = t
 *---------------------------------------------------------------------------*)
val AND_CLAUSES =
   let val t = --`t:bool`--
   in
   GEN t (CONJ
           (SPEC t AND_CLAUSE1)
            (CONJ
             (SPEC t AND_CLAUSE2)
              (CONJ
               (SPEC t AND_CLAUSE3)
                 (CONJ (SPEC t AND_CLAUSE4)
                       (SPEC t AND_CLAUSE5)))))
   end;

val _ = save_thm("AND_CLAUSES", AND_CLAUSES);

(*---------------------------------------------------------------------------
 *   |- !t. (T \/ t) = T
 *---------------------------------------------------------------------------*)
val OR_CLAUSE1 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`T \/ ^t`--) TRUTH
       and th2 = DISCH (--`T`--) (DISJ1 TRUTH t)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (t \/ T) = T
 *---------------------------------------------------------------------------*)
val OR_CLAUSE2 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t \/ T`--) TRUTH
       and th2 = DISCH (--`T`--) (DISJ2 t TRUTH)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *    |- (F \/ t) = t
 *---------------------------------------------------------------------------*)
val OR_CLAUSE3 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`F \/ ^t`--) (DISJ_CASES (ASSUME (--`F \/ ^t`--))
                                        (UNDISCH (SPEC t FALSITY))
                                        (ASSUME t))
       and th2 = SPEC t (SPEC (--`F`--) OR_INTRO_THM2)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *    |- !t. (t \/ F) = t
 *---------------------------------------------------------------------------*)
val OR_CLAUSE4 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t \/ F`--) (DISJ_CASES (ASSUME (--`^t \/ F`--))
                                             (ASSUME t)
                                             (UNDISCH (SPEC t FALSITY)))
       and th2 = SPEC (--`F`--) (SPEC t OR_INTRO_THM1)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 *   |- !t. (t \/ t) = t
 *---------------------------------------------------------------------------*)
val OR_CLAUSE5 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`^t \/ ^t`--)
                  (DISJ_CASES(ASSUME (--`^t \/ ^t`--)) (ASSUME t) (ASSUME t))
       and th2 = DISCH t (DISJ1(ASSUME t)t)
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;

(*---------------------------------------------------------------------------
 * |- !t. (T \/ t) = T /\
 *        (t \/ T) = T /\
 *        (F \/ t) = t /\
 *        (t \/ F) = t /\
 *        (t \/ t) = t
 *---------------------------------------------------------------------------*)
val OR_CLAUSES =
   let val t = --`t:bool`--
   in
   GEN t (CONJ
          (SPEC t OR_CLAUSE1)
          (CONJ
           (SPEC t OR_CLAUSE2)
           (CONJ
            (SPEC t OR_CLAUSE3)
            (CONJ (SPEC t OR_CLAUSE4)
                  (SPEC t OR_CLAUSE5)))))
   end;

val _ = save_thm("OR_CLAUSES", OR_CLAUSES);


(*---------------------------------------------------------------------------
 *  |- !t. (T ==> t) = t
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE1 =
   let val t = --`t:bool`--
       val th1 = DISCH (--`T ==> ^t`--) (MP (ASSUME (--`T ==> ^t`--)) TRUTH)
       and th2 = DISCH t (DISCH (--`T`--) (ADD_ASSUM (--`T`--) (ASSUME t)))
       and th3 = SPEC t (SPEC (--`T ==> ^t`--) IMP_ANTISYM_AX)
   in
   GEN t (MP (MP th3 th1) th2)
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (F ==> t) = T
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE2 =
   let val t = --`t:bool`--
   in
   GEN t (EQT_INTRO(SPEC t FALSITY))
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (t ==> T) = T
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE3 =
   let val t = --`t:bool`--
   in
   GEN t (EQT_INTRO(DISCH t (ADD_ASSUM t TRUTH)))
   end;

(*---------------------------------------------------------------------------
 *  |- ((T ==> F) = F) /\ ((F ==> F) = T)
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE4 =
   let val th1 = DISCH (--`T ==> F`--) (MP (ASSUME (--`T ==> F`--)) TRUTH)
       and th2 = SPEC (--`T ==> F`--) FALSITY
       and th3 = EQT_INTRO(DISCH (--`F`--) (ASSUME (--`F`--)))
   in
   CONJ(MP (MP (SPEC (--`F`--)
               (SPEC (--`T ==> F`--) IMP_ANTISYM_AX)) th1) th2) th3
   end;

(*---------------------------------------------------------------------------
 *  |- !t. (t ==> F) = ~t
 *---------------------------------------------------------------------------*)
val IMP_CLAUSE5 =
    let val t = --`t:bool`--
        val th1 = SPEC t IMP_F
        and th2 = SPEC t F_IMP
    in
    GEN t (IMP_ANTISYM_RULE th1 th2)
    end;

(*---------------------------------------------------------------------------
 *  |- !t. (T ==> t) = t /\
 *         (t ==> T) = T /\
 *         (F ==> t) = T /\
 *         (t ==> t) = t /\
 *         (t ==> F) = ~t
 *---------------------------------------------------------------------------*)
val IMP_CLAUSES =
   let val t = --`t:bool`--
   in GEN t
      (CONJ (SPEC t IMP_CLAUSE1)
            (CONJ (SPEC t IMP_CLAUSE3)
                  (CONJ (SPEC t IMP_CLAUSE2)
                        (CONJ (EQT_INTRO(DISCH t (ASSUME t)))
                              (SPEC t IMP_CLAUSE5)))))
   end;

val _ = save_thm("IMP_CLAUSES", IMP_CLAUSES);


(*----------------------------------------------------------------------------
 *    |- (~~t = t) /\ (~T = F) /\ (~F = T)
 *---------------------------------------------------------------------------*)
val NOT_CLAUSES =
 CONJ
  (GEN (--`t:bool`--)
    (IMP_ANTISYM_RULE
      (DISJ_IMP(IMP_ELIM(DISCH (--`t:bool`--) (ASSUME (--`t:bool`--)))))
      (DISCH (--`t:bool`--)
       (NOT_INTRO(DISCH (--`~t`--) (UNDISCH (NOT_ELIM(ASSUME (--`~t`--)))))))))
  (CONJ (IMP_ANTISYM_RULE
          (DISCH (--`~T`--)
                 (MP (MP (SPEC (--`T`--) F_IMP) (ASSUME (--`~T`--))) TRUTH))
          (SPEC (--`~T`--) FALSITY))
        (IMP_ANTISYM_RULE (DISCH (--`~F`--) TRUTH)
                          (DISCH (--`T`--) (MP (SPEC (--`F`--) IMP_F)
                                               (SPEC (--`F`--) FALSITY)))));

val _ = save_thm("NOT_CLAUSES", NOT_CLAUSES);

(*---------------------------------------------------------------------------
 *   |- !x. x=x
 *---------------------------------------------------------------------------*)
val EQ_REFL = GEN (--`x : 'a`--) (REFL (--`x : 'a`--));

val _ = save_thm("EQ_REFL", EQ_REFL);

(*---------------------------------------------------------------------------
 *   |- !x. (x=x) = T
 *---------------------------------------------------------------------------*)
val REFL_CLAUSE = GEN (--`x: 'a`--) (EQT_INTRO(SPEC (--`x:'a`--) EQ_REFL));

val _ = save_thm("REFL_CLAUSE", REFL_CLAUSE );

(*---------------------------------------------------------------------------
 *   |- !x y. x=y  ==>  y=x
 *---------------------------------------------------------------------------*)
val EQ_SYM =
 let val x = --`x:'a`--
     and y = --`y:'a`--
 in
   GEN x (GEN y (DISCH (--`^x = ^y`--) (SYM(ASSUME (--`^x = ^y`--)))))
 end;

val _ = save_thm("EQ_SYM",EQ_SYM);

(*---------------------------------------------------------------------------
 *    |- !x y. (x = y) = (y = x)
 *---------------------------------------------------------------------------*)
val EQ_SYM_EQ =
   GEN (--`x:'a`--)
    (GEN (--`y:'a`--)
      (IMP_ANTISYM_RULE (SPEC (--`y:'a`--) (SPEC (--`x:'a`--) EQ_SYM))
                        (SPEC (--`x:'a`--) (SPEC (--`y:'a`--) EQ_SYM))));

val _ = save_thm("EQ_SYM_EQ",EQ_SYM_EQ);

(*---------------------------------------------------------------------------
 *    |- !f g. (!x. f x = g x)  ==>  f=g
 *---------------------------------------------------------------------------*)
val EQ_EXT =
   let val f = (--`f:'a->'b`--)
       and g = (--`g: 'a -> 'b`--)
   in
   GEN f (GEN g (DISCH (--`!x:'a. ^f (x:'a) = ^g (x:'a)`--)
                       (EXT(ASSUME (--`!x:'a. ^f (x:'a) = ^g (x:'a)`--)))))
   end;

val _ = save_thm("EQ_EXT",EQ_EXT);

(*---------------------------------------------------------------------------
 *    |- !x y z. x=y  /\  y=z  ==>  x=z
 *---------------------------------------------------------------------------*)
val EQ_TRANS =
   let val x = --`x:'a`--
       and y = --`y:'a`--
       and z = --`z:'a`--
       val xyyz  = (--`(^x = ^y) /\ (^y = ^z)`--)
   in
   GEN x
    (GEN y
     (GEN z
      (DISCH xyyz
       (TRANS (CONJUNCT1(ASSUME xyyz))
              (CONJUNCT2(ASSUME xyyz))))))
   end;

val _ = save_thm("EQ_TRANS",EQ_TRANS);

(*---------------------------------------------------------------------------
 *     |- ~(T=F) /\ ~(F=T)
 *---------------------------------------------------------------------------*)
val BOOL_EQ_DISTINCT =
   let val TF = --`T = F`--
       and FT = --`F = T`--
   in
   CONJ
    (NOT_INTRO(DISCH TF (EQ_MP (ASSUME TF) TRUTH)))
    (NOT_INTRO(DISCH FT (EQ_MP (SYM(ASSUME FT)) TRUTH)))
   end;

val _ = save_thm("BOOL_EQ_DISTINCT", BOOL_EQ_DISTINCT);


(*---------------------------------------------------------------------------
 *     |- !t. (T = t) = t
 *---------------------------------------------------------------------------*)
val EQ_CLAUSE1 =
   let val t = --`t:bool`--
       val Tt = --`T = ^t`--
       val th1 = DISCH Tt (EQ_MP (ASSUME Tt) TRUTH)
       and th2 = DISCH t (SYM(EQT_INTRO(ASSUME t)))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t. (t = T) = t
 *---------------------------------------------------------------------------*)
val EQ_CLAUSE2 =
   let val t = --`t:bool`--
       val tT = --`^t = T`--
       val th1 = DISCH tT (EQ_MP (SYM (ASSUME tT)) TRUTH)
       and th2 = DISCH t (EQT_INTRO(ASSUME t))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *    |- !t. (F = t) = ~t
 *---------------------------------------------------------------------------*)
val EQ_CLAUSE3 =
   let val t = --`t:bool`--
       val Ft = --`F = ^t`--
       val tF = --`^t = F`--
       val th1 = DISCH Ft (MP (SPEC t IMP_F)
                              (DISCH t (EQ_MP(SYM(ASSUME Ft))
                                             (ASSUME t))))
       and th2 = IMP_TRANS (SPEC t NOT_F)
                           (DISCH tF (SYM(ASSUME tF)))
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t. (t = F) = ~t
 *---------------------------------------------------------------------------*)
val EQ_CLAUSE4 =
   let val t = --`t:bool`--
       val tF = --`^t = F`--
       val th1 = DISCH tF (MP (SPEC t IMP_F)
                              (DISCH t (EQ_MP(ASSUME tF)
                                             (ASSUME t))))
       and th2 = SPEC t NOT_F
   in
   GEN t (IMP_ANTISYM_RULE th1 th2)
   end;


(*---------------------------------------------------------------------------
 *  |- !t.  (T = t)  =  t  /\
 *          (t = T)  =  t  /\
 *          (F = t)  =  ~t /\
 *          (t = F)  =  ~t
 *---------------------------------------------------------------------------*)
val EQ_CLAUSES =
   let val t = --`t:bool`--
   in
   GEN t (CONJ
           (SPEC t EQ_CLAUSE1)
            (CONJ
              (SPEC t EQ_CLAUSE2)
                (CONJ (SPEC t EQ_CLAUSE3)
                      (SPEC t EQ_CLAUSE4))))
   end;

val _ = save_thm("EQ_CLAUSES", EQ_CLAUSES);


(*---------------------------------------------------------------------------
 *    |- !t1 t2 :'a. COND T t1 t2 = t1
 *---------------------------------------------------------------------------*)
val COND_CLAUSE1 =
 let val (x,t1,t2,v) = (Term`x:'a`, Term`t1:'a`,
                        Term`t2:'a`, genvar Type.bool)
     val th1 = RIGHT_BETA(AP_THM
                 (RIGHT_BETA(AP_THM
                    (RIGHT_BETA(AP_THM COND_DEF (--`T`--))) t1))t2)
     val TT = EQT_INTRO(REFL (--`T`--))
     val th2 = SUBST [v |-> SYM TT]
                     (--`(^v ==> (^x=^t1)) = (^x=^t1)`--)
                     (CONJUNCT1 (SPEC (--`^x=^t1`--) IMP_CLAUSES))
     and th3 = DISCH (--`T=F`--)
                     (MP (SPEC (--`^x=^t2`--) FALSITY)
                         (UNDISCH(MP (SPEC (--`T=F`--) F_IMP)
                                     (CONJUNCT1 BOOL_EQ_DISTINCT))))
     val th4 = DISCH (--`^x=^t1`--)
                     (CONJ(EQ_MP(SYM th2)(ASSUME (--`^x=^t1`--)))th3)
     and th5 = DISCH (--`((T=T) ==> (^x=^t1))/\((T=F) ==> (^x=^t2))`--)
                     (MP (CONJUNCT1(ASSUME (--`((T=T) ==> (^x=^t1))/\
                                               ((T=F) ==> (^x=^t2))`--)))
                         (REFL (--`T`--)))
     val th6 = MP (MP (SPEC (--`((T=T) ==> (^x=^t1))/\((T=F) ==> (^x=^t2))`--)
                            (SPEC (--`^x=^t1`--) IMP_ANTISYM_AX))
                      th4)
                  th5
     val th7 = TRANS th1 (SYM(SELECT_EQ x th6))
     val th8 = EQ_MP (SYM(BETA_CONV (--`(\^x.^x = ^t1) ^t1`--))) (REFL t1)
     val th9 = MP (SPEC t1 (SPEC (--`\^x.^x = ^t1`--) SELECT_AX)) th8
 in
   GEN t1 (GEN t2 (TRANS th7 (EQ_MP (BETA_CONV(concl th9)) th9)))
 end;


(*---------------------------------------------------------------------------
 *    |- !tm1 tm2:'a. COND F tm1 tm2 = tm2
 *
 *   Note that there is a bound variable conflict if we use use t1
 *   and t2 as the variable names. That would be a good test of the
 *   substitution algorithm.
 *---------------------------------------------------------------------------*)
val COND_CLAUSE2 =
   let val (x,t1,t2,v) = (--`x:'a`--,  --`tm1:'a`--, --`tm2:'a`--,
                          genvar (==`:bool`==))
       val th1 = RIGHT_BETA(AP_THM
                   (RIGHT_BETA(AP_THM
                     (RIGHT_BETA(AP_THM COND_DEF (--`F`--))) t1))t2)
       val FF = EQT_INTRO(REFL (--`F`--))
       val th2 = SUBST [v |-> SYM FF]
                       (--`(^v ==> (^x=^t2))=(^x=^t2)`--)
                       (CONJUNCT1(SPEC (--`^x=^t2`--) IMP_CLAUSES))
       and th3 = DISCH (--`F=T`--) (MP (SPEC (--`^x=^t1`--) FALSITY)
                                 (UNDISCH (MP (SPEC (--`F=T`--) F_IMP)
                                              (CONJUNCT2 BOOL_EQ_DISTINCT))))
       val th4 = DISCH (--`^x=^t2`--)
                       (CONJ th3 (EQ_MP(SYM th2)(ASSUME (--`^x=^t2`--))))
       and th5 = DISCH (--`((F=T) ==> (^x=^t1)) /\ ((F=F) ==> (^x=^t2))`--)
                       (MP (CONJUNCT2(ASSUME (--`((F=T) ==> (^x=^t1)) /\
                                                 ((F=F) ==> (^x=^t2))`--)))
                           (REFL (--`F`--)))
       val th6 = MP (MP (SPEC (--`((F=T) ==> (^x=^t1)) /\
                                  ((F=F) ==> (^x=^t2))`--)
                              (SPEC (--`^x=^t2`--) IMP_ANTISYM_AX))
                        th4)
                    th5
       val th7 = TRANS th1 (SYM(SELECT_EQ x th6))
       val th8 = EQ_MP (SYM(BETA_CONV (--`(\^x.^x = ^t2) ^t2`--)))
                       (REFL t2)
       val th9 = MP (SPEC t2 (SPEC (--`\^x.^x = ^t2`--) SELECT_AX)) th8
   in
     GEN t1 (GEN t2 (TRANS th7 (EQ_MP (BETA_CONV(concl th9)) th9)))
   end;


(*---------------------------------------------------------------------------
 *    |- !t1:'a.!t2:'a. ((T => t1 | t2) = t1) /\ ((F => t1 | t2) = t2)
 *---------------------------------------------------------------------------*)
val COND_CLAUSES =
   let val (t1,t2) = (--`t1:'a`--, --`t2:'a`--)
   in
   GEN t1 (GEN t2 (CONJ(SPEC t2(SPEC t1 COND_CLAUSE1))
                       (SPEC t2(SPEC t1 COND_CLAUSE2))))
   end;

val _ = save_thm("COND_CLAUSES", COND_CLAUSES);


(*--------------------------------------------------------------------- *)
(* |- b. !t. (b => t | t) = t						*)
(*					                   TFM 90.07.23 *)
(*--------------------------------------------------------------------- *)

val COND_ID =
   let val b = --`b:bool`--
       and t = --`t:'a`--
       val def = INST_TYPE [==`:'b`==  |->  ==`:'a`==] COND_DEF
       val th1 = itlist (fn x => RIGHT_BETA o (C AP_THM x))
                        [t,t,b] def
       val p = genvar (==`:bool`==)
       val asm1 = ASSUME (--`((^b=T)==>^p) /\ ((^b=F)==>^p)`--)
       val th2 = DISJ_CASES (SPEC b BOOL_CASES_AX)
                            (UNDISCH (CONJUNCT1 asm1))
                            (UNDISCH (CONJUNCT2 asm1))
       val imp1 = DISCH (concl asm1) th2
       val asm2 = ASSUME p
       val imp2 = DISCH p (CONJ (DISCH (--`^b=T`--)
                                       (ADD_ASSUM (--`^b=T`--) asm2))
	                        (DISCH (--`^b=F`--)
                                       (ADD_ASSUM (--`^b=F`--) asm2)))
       val lemma = SPEC (--`x:'a = ^t`--)
                        (GEN p (IMP_ANTISYM_RULE imp1 imp2))
       val th3 = TRANS th1 (SELECT_EQ (--`x:'a`--) lemma)
       val th4 = EQ_MP (SYM(BETA_CONV (--`(\x.x = ^t) ^t`--)))
                       (REFL t)
       val th5 = MP (SPEC t (SPEC (--`\x.x = ^t` --) SELECT_AX)) th4
       val lemma2 = EQ_MP (BETA_CONV(concl th5)) th5
   in
     GEN b (GEN t (TRANS th3 lemma2))
   end;

val _ = save_thm("COND_ID", COND_ID);

(* ---------------------------------------------------------------------*)
(* SELECT_REFL = |- !x. (@y. y = x) = x                                 *)
(* ---------------------------------------------------------------------*)

val SELECT_REFL =
  let val th1 = SPEC (--`x:'a`--)
                      (SPEC (--`\y:'a. y = x`--) SELECT_AX)
      val ths = map BETA_CONV [--`(\y:'a. y = x) x`--,
                               --`(\y:'a. y = x)(@y. y = x)`--]
      val th2 = SUBST[Term`u:bool` |-> el 1 ths, Term`v:bool` |-> el 2 ths]
                     (Term`u ==> v`) th1
  in
  GEN (--`x:'a`--) (MP th2 (REFL (--`x:'a`--)))
  end;

val _ = save_thm("SELECT_REFL", SELECT_REFL);

(*---------------------------------------------------------------------------*)
(* SELECT_UNIQUE = |- !P x. (!y. P y = (y = x)) ==> ($@ P = x)               *)
(*---------------------------------------------------------------------------*)

val SELECT_UNIQUE =
  let fun mksym tm = DISCH tm (SYM(ASSUME tm))
      val th0 = IMP_ANTISYM_RULE (mksym (--`y:'a = x`--))
                                 (mksym (--`x:'a = y`--))
      val th1 = SPEC (--`y:'a`--) (ASSUME (--`!y:'a. P y = (y = x)`--))
      val th2 = EXT(GEN (--`y:'a`--) (TRANS th1 th0))
      val th3 = AP_TERM (--`$@ :('a->bool)->'a`--) th2
      val th4 = TRANS (BETA_CONV (--`(\y:'a. y = x) y`--)) th0
      val th5 = AP_TERM (--`$@ :('a->bool)->'a`--) (EXT(GEN (--`y:'a`--) th4))
      val th6 = TRANS (TRANS th3 (SYM th5)) (SPEC (--`x:'a`--) SELECT_REFL)
  in
  GENL [(--`P:'a->bool`--), (--`x:'a`--)]
       (DISCH (--`!y:'a. P y = (y = x)`--) th6)
  end;

val _ = save_thm("SELECT_UNIQUE", SELECT_UNIQUE);

(* -------------------------------------------------------------------------*)
(* NOT_FORALL_THM = |- !P. ~(!x. P x) = ?x. ~P x                   	    *)
(* -------------------------------------------------------------------------*)

val NOT_FORALL_THM =
    let val f = (--`P:'a->bool`--)
	val x = (--`x:'a`--)
	val t = mk_comb{Rator=f,Rand=x}
	val all = mk_forall{Bvar=x,Body=t}
	and exists = mk_exists{Bvar=x,Body=mk_neg t}
	val nott = ASSUME (mk_neg t)
	val th1 = DISCH all (MP nott (SPEC x (ASSUME all)))
	val imp1 = DISCH exists (CHOOSE (x, ASSUME exists) (NOT_INTRO th1))
	val th2 =
	    CCONTR t (MP (ASSUME(mk_neg exists)) (EXISTS(exists,x)nott))
	val th3 = CCONTR exists (MP (ASSUME (mk_neg all)) (GEN x th2))
	val imp2 = DISCH (mk_neg all) th3
    in
	GEN f (IMP_ANTISYM_RULE imp2 imp1)
    end;

val _ = save_thm("NOT_FORALL_THM",NOT_FORALL_THM);


(* ------------------------------------------------------------------------- *)
(* NOT_EXISTS_THM = |- !P. ~(?x. P x) = (!x. ~P x)                   	    *)
(* ------------------------------------------------------------------------- *)

val NOT_EXISTS_THM =
    let val f = (--`P:'a->bool`--)
	val x = (--`x:'a`--)
	val t = mk_comb{Rator=f,Rand=x}
	val tm = mk_neg(mk_exists{Bvar=x,Body=t})
	val all = mk_forall{Bvar=x,Body=mk_neg t}
	val asm1 = ASSUME t
	val thm1 = MP (ASSUME tm) (EXISTS (rand tm, x) asm1)
	val imp1 = DISCH tm (GEN x (NOT_INTRO (DISCH t thm1)))
	val asm2 = ASSUME  all and asm3 = ASSUME (rand tm)
	val thm2 = DISCH (rand tm) (CHOOSE (x,asm3) (MP (SPEC x asm2) asm1))
	val imp2 = DISCH all (NOT_INTRO thm2)
    in
	GEN f (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("NOT_EXISTS_THM",NOT_EXISTS_THM);


(* ------------------------------------------------------------------------- *)
(* FORALL_AND_THM |- !P Q. (!x. P x /\ Q x) = ((!x. P x) /\ (!x. Q x))       *)
(* ------------------------------------------------------------------------- *)

val FORALL_AND_THM =
    let val f = (--`P:'a->bool`--)
	val g = (--`Q:'a->bool`--)
	val x = (--`x:'a`--)
	val th1 = ASSUME (--`!x:'a. (P x) /\ (Q x)`--)
	val imp1 =
	    (uncurry CONJ) ((GEN x ## GEN x) (CONJ_PAIR (SPEC x th1)))
	val th2 = ASSUME (--`(!x:'a. P x) /\ (!x:'a. Q x)`--)
	val imp2 =
	    GEN x (uncurry CONJ ((SPEC x ## SPEC x) (CONJ_PAIR th2)))
    in
	    GENL [f,g] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2))
    end;

val _ = save_thm("FORALL_AND_THM",FORALL_AND_THM);



(* ------------------------------------------------------------------------- *)
(* LEFT_AND_FORALL_THM = |- !P Q. (!x. P x) /\ Q = (!x. P x /\ Q)            *)
(* ------------------------------------------------------------------------- *)

val LEFT_AND_FORALL_THM =
    let val x = (--`x:'a`--)
	val f = (--`P:'a->bool`--)
	val Q = (--`Q:bool`--)
	val th1 = ASSUME (--`(!x:'a. P x) /\ Q`--)
	val imp1 = GEN x ((uncurry CONJ) ((SPEC x ## I) (CONJ_PAIR th1)))
	val th2 = ASSUME (--`!x:'a. P x /\ Q`--)
	val imp2 = (uncurry CONJ) ((GEN x ## I) (CONJ_PAIR (SPEC x th2)))
    in
	GENL [f,Q] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2))
    end;

val _ = save_thm("LEFT_AND_FORALL_THM",LEFT_AND_FORALL_THM);


(* ------------------------------------------------------------------------- *)
(* RIGHT_AND_FORALL_THM = |- !P Q. P /\ (!x. Q x) = (!x. P /\ Q x)           *)
(* ------------------------------------------------------------------------- *)

val RIGHT_AND_FORALL_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val th1 = ASSUME (--`P /\ (!x:'a. Q x)`--)
	val imp1 = GEN x ((uncurry CONJ) ((I ## SPEC x) (CONJ_PAIR th1)))
	val th2 = ASSUME (--`!x:'a. P /\ Q x`--)
	val imp2 = (uncurry CONJ) ((I ## GEN x) (CONJ_PAIR (SPEC x th2)))
    in
	GENL [P,g] (IMP_ANTISYM_RULE (DISCH_ALL imp1) (DISCH_ALL imp2))
    end;

val _ = save_thm("RIGHT_AND_FORALL_THM",RIGHT_AND_FORALL_THM);


(* ------------------------------------------------------------------------- *)
(* EXISTS_OR_THM |- !P Q. (?x. P x \/ Q x) = ((?x. P x) \/ (?x. Q x))        *)
(* ------------------------------------------------------------------------- *)

val EXISTS_OR_THM =
    let val f = (--`P:'a->bool`--)
	val g = (--`Q:'a->bool`--)
	val x = (--`x:'a`--)
	val P = mk_comb{Rator=f,Rand=x}
	val Q = mk_comb{Rator=g,Rand=x}
	val tm = mk_exists {Bvar=x,Body=mk_disj{disj1=P,disj2=Q}}
	val ep = mk_exists{Bvar=x,Body=P}
	and eq = mk_exists{Bvar=x,Body=Q}
	val Pth = EXISTS(ep,x)(ASSUME P)
	and Qth = EXISTS(eq,x)(ASSUME Q)
	val thm1 = DISJ_CASES_UNION (ASSUME(mk_disj{disj1=P,disj2=Q})) Pth Qth
	val imp1 = DISCH tm (CHOOSE (x,ASSUME tm) thm1)
	val t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q)
	val th1 = EXISTS(tm,x) t1 and th2 = EXISTS(tm,x) t2
	val e1 = CHOOSE (x,ASSUME ep) th1 and e2 = CHOOSE (x,ASSUME eq) th2
	val thm2 = DISJ_CASES (ASSUME(mk_disj{disj1=ep,disj2=eq})) e1 e2
	val imp2 = DISCH (mk_disj{disj1=ep,disj2=eq}) thm2
    in
	GENL [f,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("EXISTS_OR_THM",EXISTS_OR_THM);


(* ------------------------------------------------------------------------- *)
(* LEFT_OR_EXISTS_THM = |- (?x. P x) \/ Q = (?x. P x \/ Q)                   *)
(* ------------------------------------------------------------------------- *)

val LEFT_OR_EXISTS_THM =
    let val x = (--`x:'a`--)
	val Q = (--`Q:bool`--)
	val f = (--`P:'a->bool`--)
	val P = mk_comb{Rator=f,Rand=x}
	val ep = mk_exists{Bvar=x,Body=P}
	val tm = mk_disj{disj1=ep,disj2=Q}
	val otm = mk_exists{Bvar=x,Body=mk_disj{disj1=P,disj2=Q}}
	val t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q)
	val th1 = EXISTS(otm,x) t1 and th2 = EXISTS(otm,x) t2
	val thm1 = DISJ_CASES (ASSUME tm) (CHOOSE(x,ASSUME ep)th1) th2
	val imp1 = DISCH tm thm1
	val Pth = EXISTS(ep,x)(ASSUME P) and Qth = ASSUME Q
	val thm2 = DISJ_CASES_UNION (ASSUME(mk_disj{disj1=P,disj2=Q})) Pth Qth
	val imp2 = DISCH otm (CHOOSE (x,ASSUME otm) thm2)
    in
	GENL [f,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("LEFT_OR_EXISTS_THM",LEFT_OR_EXISTS_THM);


(* ------------------------------------------------------------------------- *)
(* RIGHT_OR_EXISTS_THM = |- P \/ (?x. Q x) = (?x. P \/ Q x)                  *)
(* ------------------------------------------------------------------------- *)

val RIGHT_OR_EXISTS_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val Q = mk_comb{Rator=g,Rand=x}
	val eq = mk_exists{Bvar=x,Body=Q}
	val tm = mk_disj{disj1=P,disj2=eq}
	val otm = mk_exists{Bvar=x,Body=mk_disj{disj1=P,disj2=Q}}
	val t1 = DISJ1 (ASSUME P) Q and t2 = DISJ2 P (ASSUME Q)
	val th1 = EXISTS(otm,x) t1 and th2 = EXISTS(otm,x) t2
	val thm1 = DISJ_CASES (ASSUME tm) th1 (CHOOSE(x,ASSUME eq)th2)
	val imp1 = DISCH tm thm1
	val Qth = EXISTS(eq,x)(ASSUME Q) and Pth = ASSUME P
	val thm2 = DISJ_CASES_UNION (ASSUME(mk_disj{disj1=P,disj2=Q})) Pth Qth
	val imp2 = DISCH otm (CHOOSE (x,ASSUME otm)  thm2)
    in
	    GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("RIGHT_OR_EXISTS_THM",RIGHT_OR_EXISTS_THM);


(* ------------------------------------------------------------------------- *)
(* BOTH_EXISTS_AND_THM = |- !P Q. (?x. P /\ Q) = (?x. P) /\ (?x. Q)          *)
(* ------------------------------------------------------------------------- *)

val BOTH_EXISTS_AND_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val Q = (--`Q:bool`--)
	val t = mk_conj{conj1=P,conj2=Q}
	val exi = mk_exists{Bvar=x,Body=t}
	val (t1,t2) = CONJ_PAIR (ASSUME t)
	val t11 = EXISTS ((mk_exists{Bvar=x,Body=P}),x) t1
	val t21 = EXISTS ((mk_exists{Bvar=x,Body=Q}),x) t2
	val imp1 = DISCH_ALL (CHOOSE (x,
                    ASSUME (mk_exists{Bvar=x,Body=mk_conj{conj1=P,conj2=Q}}))
		   (CONJ t11 t21))
	val th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q))
	val th22 = CHOOSE(x,ASSUME(mk_exists{Bvar=x,Body=P})) th21
	val th23 = CHOOSE(x,ASSUME(mk_exists{Bvar=x,Body=Q})) th22
	val (u1,u2) =
	    CONJ_PAIR (ASSUME (mk_conj{conj1=mk_exists{Bvar=x,Body=P},
				       conj2=mk_exists{Bvar=x,Body=Q}}))
	val th24 = PROVE_HYP u1 (PROVE_HYP u2 th23)
	val imp2 = DISCH_ALL th24
    in
	GENL [P,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("BOTH_EXISTS_AND_THM",BOTH_EXISTS_AND_THM);

(* ------------------------------------------------------------------------- *)
(* LEFT_EXISTS_AND_THM = |- !P Q. (?x. P x /\ Q) = (?x. P x) /\ Q            *)
(* ------------------------------------------------------------------------- *)

val LEFT_EXISTS_AND_THM =
    let val x = (--`x:'a`--)
	val f = (--`P:'a->bool`--)
	val P = mk_comb{Rator=f,Rand=x}
	val Q = (--`Q:bool`--)
	val t = mk_conj{conj1=P,conj2=Q}
	val exi = mk_exists{Bvar=x,Body=t}
	val (t1,t2) = CONJ_PAIR (ASSUME t)
	val t11 = EXISTS ((mk_exists{Bvar=x,Body=P}),x) t1
	val imp1 =
	    DISCH_ALL
		(CHOOSE
		 (x, ASSUME (mk_exists{Bvar=x,Body=mk_conj{conj1=P,conj2=Q}}))
		    (CONJ t11 t2))
	val th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q))
	val th22 = CHOOSE(x,ASSUME(mk_exists{Bvar=x,Body=P})) th21
	val (u1,u2) = CONJ_PAIR(ASSUME
                       (mk_conj{conj1=mk_exists{Bvar=x,Body=P}, conj2=Q}))
	val th23 = PROVE_HYP u1 (PROVE_HYP u2 th22)
	val imp2 = DISCH_ALL th23
    in
	GENL [f,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end ;

val _ = save_thm("LEFT_EXISTS_AND_THM",LEFT_EXISTS_AND_THM);

(* ------------------------------------------------------------------------- *)
(* RIGHT_EXISTS_AND_THM = |- !P Q. (?x. P /\ Q x) = P /\ (?x. Q x)           *)
(* ------------------------------------------------------------------------- *)

val RIGHT_EXISTS_AND_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val Q = mk_comb{Rator=g,Rand=x}
	val t = mk_conj{conj1=P,conj2=Q}
	val exi = mk_exists{Bvar=x,Body=t}
	val (t1,t2) = CONJ_PAIR (ASSUME t)
	val t21 = EXISTS ((mk_exists{Bvar=x,Body=Q}),x) t2
	val imp1 =
	    DISCH_ALL
		(CHOOSE
		 (x, ASSUME (mk_exists{Bvar=x,Body=mk_conj{conj1=P,conj2=Q}}))
		 (CONJ t1 t21))
	val th21 = EXISTS (exi,x) (CONJ (ASSUME P) (ASSUME Q))
	val th22 = CHOOSE(x,ASSUME(mk_exists{Bvar=x,Body=Q})) th21
	val (u1,u2) = CONJ_PAIR (ASSUME
                        (mk_conj{conj1=P, conj2=mk_exists{Bvar=x,Body=Q}}))
	val th23 = PROVE_HYP u1 (PROVE_HYP u2 th22)
	val imp2 = DISCH_ALL th23
    in
	GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("RIGHT_EXISTS_AND_THM",RIGHT_EXISTS_AND_THM);


(* ------------------------------------------------------------------------- *)
(* BOTH_FORALL_OR_THM = |- !P Q. (!x. P \/ Q) = (!x. P) \/ (!x. Q)           *)
(* ------------------------------------------------------------------------- *)

val BOTH_FORALL_OR_THM =
  let val x = (--`x:'a`--)
      val P = (--`P:bool`--)
      val Q = (--`Q:bool`--)
      val imp11 = DISCH_ALL (SPEC x (ASSUME (mk_forall{Bvar=x,Body=P})))
      val imp12 = DISCH_ALL (GEN x (ASSUME P))
      val fath = IMP_ANTISYM_RULE imp11 imp12
      val th1 = REFL (mk_forall{Bvar=x, Body=mk_disj{disj1=P,disj2=Q}})
      val th2 = CONV_RULE (RAND_CONV
                 (K (INST [P |-> mk_disj{disj1=P,disj2=Q}] fath))) th1
      val th3 = CONV_RULE(RAND_CONV(RATOR_CONV(RAND_CONV(K(SYM fath))))) th2
      val th4 = CONV_RULE(RAND_CONV(RAND_CONV(K(SYM(INST[P|->Q] fath))))) th3
  in
    GENL [P,Q] th4
  end;

val _ = save_thm("BOTH_FORALL_OR_THM",BOTH_FORALL_OR_THM);

(* ------------------------------------------------------------------------- *)
(* LEFT_FORALL_OR_THM = |- !P Q. (!x. P x \/ Q) = (!x. P x) \/ Q             *)
(* ------------------------------------------------------------------------- *)

val LEFT_FORALL_OR_THM =
  let val x = (--`x:'a`--)
      val f = (--`P:'a->bool`--)
      val P = mk_comb{Rator=f,Rand=x}
      val Q = (--`Q:bool`--)
      val tm = (mk_forall{Bvar=x,Body=mk_disj{disj1=P,disj2=Q}})
      val thm1 = SPEC x (ASSUME tm)
      val thm2 = CONTR P (MP (ASSUME (mk_neg Q)) (ASSUME Q))
      val thm3 = DISJ1 (GEN x (DISJ_CASES thm1 (ASSUME P) thm2)) Q
      val thm4 = DISJ2 (mk_forall{Bvar=x,Body=P}) (ASSUME Q)
      val imp1 = DISCH tm (DISJ_CASES (SPEC Q EXCLUDED_MIDDLE) thm4 thm3)
      val thm5 = SPEC x (ASSUME (mk_forall{Bvar=x,Body=P}))
      val thm6 = ASSUME Q
      val imp2 = DISCH_ALL (GEN x (DISJ_CASES_UNION
                  (ASSUME(mk_disj{disj1=mk_forall{Bvar=x,Body=P}, disj2=Q}))
                   thm5 thm6))
  in
      GENL [Q,f] (IMP_ANTISYM_RULE imp1 imp2)
  end;

val _ = save_thm("LEFT_FORALL_OR_THM",LEFT_FORALL_OR_THM);

(* ------------------------------------------------------------------------- *)
(* RIGHT_FORALL_OR_THM = |- !P Q. (!x. P \/ Q x) = P \/ (!x. Q x)            *)
(* ------------------------------------------------------------------------- *)

val RIGHT_FORALL_OR_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val Q = mk_comb{Rator=g,Rand=x}
	val tm = (mk_forall{Bvar=x,Body=mk_disj{disj1=P,disj2=Q}})
	val thm1 = SPEC x (ASSUME tm)
	val thm2 = CONTR Q (MP (ASSUME (mk_neg P)) (ASSUME P))
	val thm3 = DISJ2 P (GEN x (DISJ_CASES thm1 thm2 (ASSUME Q)))
	val thm4 = DISJ1 (ASSUME P) (mk_forall{Bvar=x,Body=Q})
	val imp1 = DISCH tm (DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm4 thm3)
	val thm5 = ASSUME P
	val thm6 = SPEC x (ASSUME (mk_forall{Bvar=x,Body=Q}))
	val imp2 = DISCH_ALL (GEN x (DISJ_CASES_UNION
                   (ASSUME (mk_disj{disj1=P, disj2=mk_forall{Bvar=x,Body=Q}}))
                   thm5 thm6))
    in
	    GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("RIGHT_FORALL_OR_THM",RIGHT_FORALL_OR_THM);


(* ------------------------------------------------------------------------- *)
(* BOTH_FORALL_IMP_THM = |- (!x. P ==> Q) = ((?x.P) ==> (!x.Q))              *)
(* ------------------------------------------------------------------------- *)

val BOTH_FORALL_IMP_THM =
    let val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val Q = (--`Q:bool`--)
	val tm = mk_forall{Bvar=x, Body=mk_imp{ant=P,conseq= Q}}
	val asm = mk_exists{Bvar=x,Body=P}
	val th1 = GEN x (CHOOSE(x,ASSUME asm)(UNDISCH(SPEC x (ASSUME tm))))
	val imp1 = DISCH tm (DISCH asm th1)
	val cncl = rand(concl imp1)
	val th2 = SPEC x (MP (ASSUME cncl) (EXISTS (asm,x) (ASSUME P)))
	val imp2 = DISCH cncl (GEN x (DISCH P th2))
    in
	GENL [P,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("BOTH_FORALL_IMP_THM",BOTH_FORALL_IMP_THM);


(* ------------------------------------------------------------------------- *)
(* LEFT_FORALL_IMP_THM = |- (!x. P[x]==>Q) = ((?x.P[x]) ==> Q)               *)
(* ------------------------------------------------------------------------- *)

val LEFT_FORALL_IMP_THM =
    let	val x = (--`x:'a`--)
	val f = (--`P:'a->bool`--)
	val P = mk_comb{Rator=f,Rand=x}
	val Q = (--`Q:bool`--)
	val tm = mk_forall{Bvar=x, Body= mk_imp {ant=P,conseq=Q}}
	val asm = mk_exists{Bvar=x,Body=P}
	val th1 = CHOOSE(x,ASSUME asm)(UNDISCH(SPEC x (ASSUME tm)))
	val imp1 = DISCH tm (DISCH asm th1)
	val cncl = rand(concl imp1)
	val th2 = MP (ASSUME cncl) (EXISTS (asm,x) (ASSUME P))
	val imp2 = DISCH cncl (GEN x (DISCH P th2))
    in
	GENL [f,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("LEFT_FORALL_IMP_THM",LEFT_FORALL_IMP_THM);

(* ------------------------------------------------------------------------- *)
(* RIGHT_FORALL_IMP_THM = |- (!x. P==>Q[x]) = (P ==> (!x.Q[x]))              *)
(* ------------------------------------------------------------------------- *)

val RIGHT_FORALL_IMP_THM =
    let val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val Q = mk_comb{Rator=g,Rand=x}
	val tm = mk_forall{Bvar=x, Body=mk_imp{ant=P,conseq=Q}}
	val imp1 = DISCH P(GEN x(UNDISCH(SPEC x(ASSUME tm))))
	val cncl = concl imp1
	val imp2 = GEN x (DISCH P(SPEC x(UNDISCH (ASSUME cncl))))
    in
	GENL [P,g] (IMP_ANTISYM_RULE (DISCH tm imp1) (DISCH cncl imp2))
    end;

val _ = save_thm("RIGHT_FORALL_IMP_THM",RIGHT_FORALL_IMP_THM);


(* ------------------------------------------------------------------------- *)
(* BOTH_EXISTS_IMP_THM = |- (?x. P ==> Q) = ((!x.P) ==> (?x.Q))              *)
(* ------------------------------------------------------------------------- *)

val BOTH_EXISTS_IMP_THM =
    let val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val Q = (--`Q:bool`--)
	val tm = mk_exists{Bvar=x,Body=mk_imp{ant=P,conseq=Q}}
	val eQ = mk_exists{Bvar=x,Body=Q}
	val aP = mk_forall{Bvar=x,Body=P}
	val thm1 = EXISTS(eQ,x)(UNDISCH(ASSUME(mk_imp{ant=P,conseq=Q})))
	val thm2 = DISCH aP (PROVE_HYP (SPEC x (ASSUME aP)) thm1)
	val imp1 = DISCH tm (CHOOSE(x,ASSUME tm) thm2)
	val thm2 = CHOOSE(x,UNDISCH (ASSUME (rand(concl imp1)))) (ASSUME Q)
	val thm3 = DISCH P (PROVE_HYP (GEN x (ASSUME P)) thm2)
	val imp2 = DISCH (rand(concl imp1)) (EXISTS(tm,x) thm3)
    in
	GENL [P,Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("BOTH_EXISTS_IMP_THM",BOTH_EXISTS_IMP_THM);


(* ------------------------------------------------------------------------- *)
(* LEFT_EXISTS_IMP_THM = |- (?x. P[x] ==> Q) = ((!x.P[x]) ==> Q)             *)
(* ------------------------------------------------------------------------- *)

val LEFT_EXISTS_IMP_THM =
    let	val x = (--`x:'a`--)
	val f = (--`P:'a->bool`--)
	val P = mk_comb{Rator=f,Rand=x}
	val Q = (--`Q:bool`--)
	val tm = mk_exists{Bvar=x, Body= mk_imp{ant=P,conseq=Q}}
	val allp = mk_forall{Bvar=x,Body=P}
	val th1 = SPEC x (ASSUME allp)
	val thm1 = MP (ASSUME(mk_imp{ant=P,conseq=Q})) th1
	val imp1 = DISCH tm (CHOOSE(x,ASSUME tm)(DISCH allp thm1))
	val otm = rand(concl imp1)
	val thm2 = EXISTS(tm,x)(DISCH P (UNDISCH(ASSUME otm)))
	val nex =  mk_exists{Bvar=x,Body=mk_neg P}
	val asm1 = EXISTS (nex, x) (ASSUME (mk_neg P))
	val th2 = CCONTR P (MP (ASSUME (mk_neg nex)) asm1)
	val th3 = CCONTR nex (MP (ASSUME (mk_neg allp)) (GEN x th2))
	val thm4 = DISCH P (CONTR Q (UNDISCH (ASSUME (mk_neg P))))
	val thm5 = CHOOSE(x,th3)(EXISTS(tm,x)thm4)
	val thm6 = DISJ_CASES (SPEC allp EXCLUDED_MIDDLE) thm2 thm5
	val imp2 = DISCH otm thm6
    in
	GENL [f, Q] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("LEFT_EXISTS_IMP_THM",LEFT_EXISTS_IMP_THM);


(* ------------------------------------------------------------------------- *)
(* RIGHT_EXISTS_IMP_THM = |- (?x. P ==> Q[x]) = (P ==> (?x.Q[x]))            *)
(* ------------------------------------------------------------------------- *)

val RIGHT_EXISTS_IMP_THM =
    let	val x = (--`x:'a`--)
	val P = (--`P:bool`--)
	val g = (--`Q:'a->bool`--)
	val Q = mk_comb{Rator=g,Rand=x}
	val tm = mk_exists{Bvar=x,Body=mk_imp{ant=P,conseq=Q}}
	val thm1 = EXISTS (mk_exists{Bvar=x,Body=Q},x)
	                   (UNDISCH(ASSUME(mk_imp{ant=P,conseq=Q})))
	val imp1 = DISCH tm (CHOOSE(x,ASSUME tm) (DISCH P thm1))
	val thm2 = UNDISCH (ASSUME (rand(concl imp1)))
	val thm3 = CHOOSE (x,thm2) (EXISTS (tm,x) (DISCH P (ASSUME Q)))
	val thm4 = EXISTS(tm,x)(DISCH P(CONTR Q(UNDISCH(ASSUME(mk_neg P)))))
	val thm5 = DISJ_CASES (SPEC P EXCLUDED_MIDDLE) thm3 thm4
	val imp2 = DISCH(rand(concl imp1)) thm5
    in
	GENL [P,g] (IMP_ANTISYM_RULE imp1 imp2)
    end;

val _ = save_thm("RIGHT_EXISTS_IMP_THM",RIGHT_EXISTS_IMP_THM);

(* --------------------------------------------------------------------- *)
(* OR_IMP_THM = |- !A B. (A = B \/ A) = (B ==> A)                        *)
(* [TFM 90.06.28]                                                        *)
(* --------------------------------------------------------------------- *)

val OR_IMP_THM =
 let val t1 = (--`A:bool`--) and t2 = (--`B:bool`--)
     val asm1 = ASSUME (--`^t1 = (^t2 \/ ^t1)`--)
     and asm2 = EQT_INTRO(ASSUME t2)
     val th1 = SUBST [t2 |-> asm2] (concl asm1) asm1
     val th2 = TRANS th1 (CONJUNCT1 (SPEC t1 OR_CLAUSES))
     val imp1 = DISCH (concl asm1) (DISCH t2 (EQT_ELIM th2))
     val asm3 = ASSUME (--`^t2 ==> ^t1`--)
     and asm4 = ASSUME (--`^t2 \/ ^t1`--)
     val th3 = DISJ_CASES asm4 (MP asm3 (ASSUME t2)) (ASSUME t1)
     val th4 = DISCH (concl asm4) th3
     and th5 = DISCH t1 (DISJ2 t2 (ASSUME t1))
     val imp2 = DISCH (--`^t2 ==> ^t1`--) (IMP_ANTISYM_RULE th5 th4)
  in
   GEN t1 (GEN t2 (IMP_ANTISYM_RULE imp1 imp2))
  end;

val _ = save_thm("OR_IMP_THM",OR_IMP_THM);

(* --------------------------------------------------------------------- *)
(* NOT_IMP = |- !A B. ~(A ==> B) = A /\ ~B                               *)
(* [TFM 90.07.09]                                                        *)
(* --------------------------------------------------------------------- *)

val NOT_IMP =
let val t1 = (--`A:bool`--) and t2 = (--`B:bool`--)
    val asm1 = ASSUME (--`~(^t1 ==> ^t2)`--)
    val thm1 = SUBST [t1 |-> EQF_INTRO (ASSUME (mk_neg t1))] (concl asm1) asm1
    val thm2 = CCONTR t1 (MP thm1 (DISCH(--`F`--)(CONTR t2 (ASSUME(--`F`--)))))
    val thm3 = SUBST [t2 |-> EQT_INTRO (ASSUME t2)] (concl asm1) asm1
    val thm4 = NOT_INTRO(DISCH t2 (MP thm3 (DISCH t1 (ADD_ASSUM t1 TRUTH))))
    val imp1 = DISCH (concl asm1) (CONJ thm2 thm4)
    val conj =  ASSUME (--`^t1 /\ ~^t2`--)
    val (asm2,asm3) = (CONJUNCT1 conj, CONJUNCT2 conj)
    val asm4 = ASSUME (--`^t1 ==> ^t2`--)
    val thm5 = MP (SUBST [t2 |-> EQF_INTRO asm3] (concl asm4) asm4) asm2
    val imp2 = DISCH (--`^t1 /\ ~ ^t2`--)
                     (NOT_INTRO(DISCH (--`^t1 ==> ^t2`--) thm5))
 in
    GEN t1 (GEN t2 (IMP_ANTISYM_RULE imp1 imp2))
 end;

val _ = save_thm("NOT_IMP", NOT_IMP);

(* --------------------------------------------------------------------- *)
(* DISJ_ASSOC: |- !A B C. A \/ B \/ C = (A \/ B) \/ C                    *)
(* --------------------------------------------------------------------- *)
fun mk_disj(x,y) = Dsyntax.mk_disj{disj1=x,disj2=y}
fun mk_conj(x,y) = Dsyntax.mk_conj{conj1=x,conj2=y};

val DISJ_ASSOC =
let val t1 = (--`A:bool`--) and t2 = (--`B:bool`--) and t3 = (--`C:bool`--)
    val at1 = DISJ1 (DISJ1 (ASSUME t1) t2) t3 and
        at2 = DISJ1 (DISJ2 t1 (ASSUME t2)) t3 and
        at3 = DISJ2 (mk_disj(t1,t2)) (ASSUME t3)
    val thm = DISJ_CASES (ASSUME (mk_disj(t2,t3))) at2 at3
    val thm1 = DISJ_CASES (ASSUME (mk_disj(t1,mk_disj(t2,t3)))) at1 thm
    val at1 = DISJ1 (ASSUME t1) (mk_disj(t2,t3)) and
        at2 = DISJ2 t1 (DISJ1 (ASSUME t2) t3) and
        at3 = DISJ2 t1 (DISJ2 t2 (ASSUME t3))
    val thm = DISJ_CASES (ASSUME (mk_disj(t1,t2))) at1 at2
    val thm2 = DISJ_CASES (ASSUME (mk_disj(mk_disj(t1,t2),t3))) thm at3
    val imp1 = DISCH (mk_disj(t1,mk_disj(t2,t3))) thm1 and
        imp2 = DISCH (mk_disj(mk_disj(t1,t2),t3)) thm2
 in
   GENL [t1,t2,t3] (IMP_ANTISYM_RULE imp1 imp2)
 end;

val _ = save_thm("DISJ_ASSOC", DISJ_ASSOC);

(* --------------------------------------------------------------------- *)
(* DISJ_SYM: |- !A B. A \/ B = B \/ A                   		 *)
(* --------------------------------------------------------------------- *)

val DISJ_SYM =
let val t1   = (--`A:bool`--) and t2 = (--`B:bool`--)
    val th1  = DISJ1 (ASSUME t1) t2 and th2 = DISJ2 t1 (ASSUME t2)
    val thm1 = DISJ_CASES (ASSUME(mk_disj(t2,t1))) th2 th1
    val th1  = DISJ1 (ASSUME t2) t1 and th2 = DISJ2 t2 (ASSUME t1)
    val thm2 = DISJ_CASES (ASSUME(mk_disj(t1,t2))) th2 th1
    val imp1 = DISCH (mk_disj(t2,t1)) thm1 and
        imp2 = DISCH (mk_disj(t1,t2)) thm2
 in
   GENL [t1,t2] (IMP_ANTISYM_RULE imp2 imp1)
 end;

val _ = save_thm("DISJ_SYM", DISJ_SYM);
val _ = save_thm("DISJ_COMM", DISJ_SYM);

(* --------------------------------------------------------------------- *)
(* DE_MORGAN_THM: 							 *)
(*  |- !A B. (~(t1 /\ t2) = ~t1 \/ ~t2) /\ (~(t1 \/ t2) = ~t1 /\ ~t2)    *)
(* --------------------------------------------------------------------- *)

val DE_MORGAN_THM =
let val t1 = (--`A:bool`--) and t2 = (--`B:bool`--)
    val thm1 =
      let val asm1 = ASSUME (--`~(^t1 /\ ^t2)`--)
          val cnj = MP asm1 (CONJ (ASSUME t1) (ASSUME t2))
          val imp1 =
            let val case1 = DISJ2 (--`~^t1`--) (NOT_INTRO(DISCH t2 cnj))
                val case2 = DISJ1 (ASSUME (--`~ ^t1`--)) (--`~ ^t2`--)
            in
              DISJ_CASES (SPEC t1 EXCLUDED_MIDDLE) case1 case2
            end
          val th1 = MP (ASSUME (--`~^t1`--))
                       (CONJUNCT1 (ASSUME (--`^t1 /\ ^t2`--)))
          val th2 = MP (ASSUME (--`~^t2`--))
                   (CONJUNCT2 (ASSUME (--`^t1 /\ ^t2`--)))
          val imp2 =
            let val fth = DISJ_CASES (ASSUME (--`~^t1 \/ ~^t2`--)) th1 th2
            in
              DISCH (--`~^t1 \/ ~^t2`--)
                    (NOT_INTRO(DISCH (--`^t1 /\ ^t2`--) fth))
            end
      in
        IMP_ANTISYM_RULE (DISCH (--`~(^t1 /\ ^t2)`--) imp1) imp2
      end
    val thm2 =
      let val asm1 = ASSUME (--`~(^t1 \/ ^t2)`--)
          val imp1 =
            let val th1 = NOT_INTRO (DISCH t1(MP asm1 (DISJ1 (ASSUME t1) t2)))
                val th2 = NOT_INTRO (DISCH t2 (MP asm1 (DISJ2 t1 (ASSUME t2))))
            in
              DISCH (--`~(^t1 \/ ^t2)`--) (CONJ th1 th2)
            end
          val imp2 =
            let val asm = ASSUME (--`^t1 \/ ^t2`--)
                val a1 = CONJUNCT1(ASSUME (--`~^t1 /\ ~^t2`--)) and
                    a2 = CONJUNCT2(ASSUME (--`~^t1 /\ ~^t2`--))
               val fth = DISJ_CASES asm (UNDISCH a1) (UNDISCH a2)
            in
                DISCH (--`~^t1 /\ ~^t2`--)
                      (NOT_INTRO(DISCH (--`^t1 \/ ^t2`--) fth))
            end
      in
        IMP_ANTISYM_RULE imp1 imp2
      end
 in
    GEN t1 (GEN t2 (CONJ thm1 thm2))
 end;

val _ = save_thm("DE_MORGAN_THM", DE_MORGAN_THM);

(* -------------------------------------------------------------------------*)
(* Distributive laws:							    *)
(*									    *)
(* LEFT_AND_OVER_OR   |- !A B C. A /\ (B \/ C) = A /\ B \/ A /\ C           *)
(*									    *)
(* RIGHT_AND_OVER_OR  |- !A B C. (B \/ C) /\ A = B /\ A \/ C /\ A           *)
(*									    *)
(* LEFT_OR_OVER_AND   |- !A B C. A \/ B /\ C = (A \/ B) /\ (A \/ C)         *)
(*									    *)
(* RIGHT_OR_OVER_AND  |- !A B C. B /\ C \/ A = (B \/ A) /\ (C \/ A)         *)
(* -------------------------------------------------------------------------*)

val LEFT_AND_OVER_OR =
    let val t1 = --`A:bool`--
        and t2 = --`B:bool`--
        and t3 = --`C:bool`--
        val (th1,th2) = CONJ_PAIR(ASSUME (mk_conj(t1,mk_disj(t2,t3))))
        val th3 = CONJ th1 (ASSUME t2) and th4 = CONJ th1 (ASSUME t3)
        val th5 = DISJ_CASES_UNION th2 th3 th4
        val imp1 = DISCH (mk_conj(t1,mk_disj(t2,t3))) th5
        val (th1,th2) = (I ## C DISJ1 t3) (CONJ_PAIR (ASSUME (mk_conj(t1,t2))))
        val (th3,th4) = (I ## DISJ2 t2) (CONJ_PAIR (ASSUME (mk_conj(t1,t3))))
        val th5 = CONJ th1 th2 and th6 = CONJ th3 th4
        val th6 = DISJ_CASES (ASSUME (rand(concl imp1))) th5 th6
        val imp2 = DISCH (rand(concl imp1)) th6
    in
      GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
    end;

val _ = save_thm("LEFT_AND_OVER_OR", LEFT_AND_OVER_OR);

val RIGHT_AND_OVER_OR =
   let val t1 = --`A:bool`--
       and t2 = --`B:bool`--
       and t3 = --`C:bool`--
       val (th1,th2) = CONJ_PAIR(ASSUME (mk_conj(mk_disj(t2,t3),t1)))
       val th3 = CONJ (ASSUME t2) th2 and th4 = CONJ (ASSUME t3) th2
       val th5 = DISJ_CASES_UNION th1 th3 th4
       val imp1 = DISCH (mk_conj(mk_disj(t2,t3),t1)) th5
       val (th1,th2) = (C DISJ1 t3 ## I) (CONJ_PAIR (ASSUME (mk_conj(t2,t1))))
       val (th3,th4) = (DISJ2 t2 ## I) (CONJ_PAIR (ASSUME (mk_conj(t3,t1))))
       val th5 = CONJ th1 th2 and th6 = CONJ th3 th4
       val th6 = DISJ_CASES (ASSUME (rand(concl imp1))) th5 th6
       val imp2 = DISCH (rand(concl imp1)) th6
   in
     GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
   end;

val _ = save_thm("RIGHT_AND_OVER_OR", RIGHT_AND_OVER_OR);

val LEFT_OR_OVER_AND =
   let val t1 = --`A:bool`--
       and t2 = --`B:bool`--
       and t3 = --`C:bool`--
       val th1 = ASSUME (mk_disj(t1,mk_conj(t2,t3)))
       val th2 = CONJ (DISJ1 (ASSUME t1) t2) (DISJ1 (ASSUME t1) t3)
       val (th3,th4) = CONJ_PAIR (ASSUME(mk_conj(t2,t3)))
       val th5 = CONJ (DISJ2 t1 th3) (DISJ2 t1 th4)
       val imp1 = DISCH (concl th1) (DISJ_CASES th1 th2 th5)
       val (th1,th2) = CONJ_PAIR (ASSUME (rand(concl imp1)))
       val th3 = DISJ1 (ASSUME t1) (mk_conj(t2,t3))
       val (th4,th5) = CONJ_PAIR (ASSUME (mk_conj(t2,t3)))
       val th4 = DISJ2 t1 (CONJ (ASSUME t2) (ASSUME t3))
       val th5 = DISJ_CASES th2 th3 (DISJ_CASES th1 th3 th4)
       val imp2 = DISCH (rand(concl imp1)) th5
   in
     GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
   end;

val _ = save_thm("LEFT_OR_OVER_AND", LEFT_OR_OVER_AND);

val RIGHT_OR_OVER_AND =
   let val t1 = --`A:bool`--
       and t2 = --`B:bool`--
       and t3 = --`C:bool`--
       val th1 = ASSUME (mk_disj(mk_conj(t2,t3),t1))
       val th2 = CONJ (DISJ2 t2 (ASSUME t1)) (DISJ2 t3 (ASSUME t1))
       val (th3,th4) = CONJ_PAIR (ASSUME(mk_conj(t2,t3)))
       val th5 = CONJ (DISJ1 th3 t1) (DISJ1 th4 t1)
       val imp1 = DISCH (concl th1) (DISJ_CASES th1 th5 th2)
       val (th1,th2) = CONJ_PAIR (ASSUME (rand(concl imp1)))
       val th3 = DISJ2 (mk_conj(t2,t3)) (ASSUME t1)
       val (th4,th5) = CONJ_PAIR (ASSUME (mk_conj(t2,t3)))
       val th4 = DISJ1 (CONJ (ASSUME t2) (ASSUME t3)) t1
       val th5 = DISJ_CASES th2 (DISJ_CASES th1 th4 th3) th3
       val imp2 = DISCH (rand(concl imp1)) th5
   in
     GEN t1 (GEN t2 (GEN t3 (IMP_ANTISYM_RULE imp1 imp2)))
   end;

val _ = save_thm("RIGHT_OR_OVER_AND", RIGHT_OR_OVER_AND);


(*---------------------------------------------------------------------------*
 * IMP_DISJ_THM = |- !A B. A ==> B = ~A \/ B                                 *
 *---------------------------------------------------------------------------*)
val IMP_DISJ_THM =
let val A = --`A:bool`--
    val B = --`B:bool`--
    val th1 = ASSUME (Term`A ==> B`)
    val th2 = ASSUME A
    val th3 = MP th1 th2
    val th4 = DISJ2 (Term`~A`) th3
    val th5 = ASSUME (Term`~A`);
    val th6 = ADD_ASSUM (Term`A ==> B`) th5
    val th7 = DISJ1 th6 B
    val th8 = SPEC A EXCLUDED_MIDDLE
    val th9 = DISJ_CASES th8 th4 th7

    val th10 = EQT_INTRO th2
    val th11 = ASSUME (Term`~A \/ B`)
    val th12 = SUBST [A |-> th10] (concl th11) th11
    val th13 = CONJUNCT1 (CONJUNCT2 NOT_CLAUSES)
    val th14 = SUBST [A |-> th13] (subst [Term`~T` |-> A] (concl th12)) th12
    val th15 = CONJUNCT1 (CONJUNCT2(CONJUNCT2 (SPEC B OR_CLAUSES)))
    val th16 = SUBST [A |-> th15] A th14
    val th17 = DISCH A th16
    val th18 = DISCH (concl th11) th17
 in
   GENL [A,B] (IMP_ANTISYM_RULE (DISCH (hd(hyp th9)) th9) th18)
 end;

val _ = save_thm ("IMP_DISJ_THM", IMP_DISJ_THM);

(*----------------------------------------------------------------------*)
(* DISJ_IMP_THM = |- !P Q R. P \/ Q ==> R = (P ==> R) /\ (Q ==> R)      *)
(*                                                         MN 99.05.06  *)
(*----------------------------------------------------------------------*)

val DISJ_IMP_THM = let
  val P = --`P:bool`--
  val Q = --`Q:bool`--
  val R = --`R:bool`--
  val lhs = --`P \/ Q ==> R`--
  val rhs = --`(P ==> R) /\ (Q ==> R)`--
  val ass_lhs = ASSUME lhs
  val ass_P = ASSUME P
  val ass_Q = ASSUME Q
  val p_imp_r = DISCH P (MP ass_lhs (DISJ1 ass_P Q))
  val q_imp_r = DISCH Q (MP ass_lhs (DISJ2 P ass_Q))
  val lr_imp = DISCH lhs (CONJ p_imp_r q_imp_r)
  (* half way there! *)
  val ass_rhs = ASSUME rhs
  val porq = (--`P \/ Q`--)
  val ass_porq = ASSUME porq
  val my_and1 = SPECL [(--`P ==> R`--), (--`Q ==> R`--)] AND1_THM
  val p_imp_r = MP my_and1 ass_rhs
  val r_from_p = MP p_imp_r ass_P
  val my_and2 = SPECL [(--`P ==> R`--), (--`Q ==> R`--)] AND2_THM
  val q_imp_r = MP my_and2 ass_rhs
  val r_from_q = MP q_imp_r ass_Q
  val rl_imp = DISCH rhs (DISCH porq (DISJ_CASES ass_porq r_from_p r_from_q))
in
  save_thm("DISJ_IMP_THM", GENL [P,Q,R] (IMP_ANTISYM_RULE lr_imp rl_imp))
end

(* ---------------------------------------------------------------------*)
(* IMP_F_EQ_F                                                           *)
(*                                                                      *)
(* |- !t. t ==> F = (t = F)					        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)
local fun nthCONJUNCT n cth =
        let val th = funpow (n-1) CONJUNCT2 cth
        in if (is_conj (concl th))
           then CONJUNCT1 th else th
        end
in
val IMP_F_EQ_F =
   GEN (--`t:bool`--)
     (TRANS (nthCONJUNCT 5 (SPEC_ALL IMP_CLAUSES))
            (SYM (nthCONJUNCT 4 (SPEC_ALL EQ_CLAUSES))))
end;

val _ = save_thm("IMP_F_EQ_F", IMP_F_EQ_F);

(* ---------------------------------------------------------------------*)
(* AND_IMP_INTRO							*)
(*								        *)
(* |- !t1 t2 t3. t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3		        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val AND_IMP_INTRO =
let val t1 = --`t1:bool`--
    and t2 = --`t2:bool`--
    and t3 = --`t3:bool`--
    and imp = --`$==>`--
    val [IMP1,IMP2,IMP3,_,IMP4] = map GEN_ALL(CONJUNCTS (SPEC_ALL IMP_CLAUSES))
    and [AND1,AND2,AND3,AND4,_] = map GEN_ALL(CONJUNCTS (SPEC_ALL AND_CLAUSES))
    val thTl = SPEC (--`t2 ==> t3`--) IMP1
    and thFl = SPEC (--`t2 ==> t3`--) IMP3
    val thTr = AP_THM (AP_TERM imp (SPEC t2 AND1)) t3
    and thFr = TRANS (AP_THM (AP_TERM imp (SPEC t2 AND3)) t3)(SPEC t3 IMP3)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm   = Term`t1 ==> t2 ==> t3 = t1 /\ t2 ==> t3`
    val thT2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = T`--)] tm tm
    and thF2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [t1,t2,t3] (DISJ_CASES (SPEC t1 BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("AND_IMP_INTRO", AND_IMP_INTRO);

(* ---------------------------------------------------------------------*)
(* EQ_IMP_THM							        *)
(*								        *)
(* |- !t1 t2. (t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1)		        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val EQ_IMP_THM =
let val t1 = --`t1:bool`--
    and t2 = --`t2:bool`--
    val conj = --`$/\`--
    val [IMP1,IMP2,IMP3,_,IMP4] = map GEN_ALL(CONJUNCTS (SPEC_ALL IMP_CLAUSES))
    and [AND1,AND2,AND3,AND4,_] = map GEN_ALL(CONJUNCTS (SPEC_ALL AND_CLAUSES))
    and [EQ1,EQ2,EQ3,EQ4] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
    val thTl = SPEC t2 EQ1
    and thFl = SPEC t2 EQ3
    val thTr = TRANS (MK_COMB (AP_TERM conj (SPEC t2 IMP1), SPEC t2 IMP2))
                     (SPEC t2 AND2)
    and thFr = TRANS (MK_COMB (AP_TERM conj (SPEC t2 IMP3), SPEC t2 IMP4))
                     (SPEC (mk_neg t2) AND1)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(t1 = t2) = (t1 ==> t2) /\ (t2 ==> t1)`--)
    val thT2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = T`--)] tm tm
    and thF2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [t1,t2] (DISJ_CASES (SPEC t1 BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("EQ_IMP_THM", EQ_IMP_THM);

(* ---------------------------------------------------------------------*)
(* EQ_EXPAND = |- !t1 t2. (t1 = t2) = ((t1 /\ t2) \/ (~t1 /\ ~t2))      *)
(*                                                         RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val EQ_EXPAND =
let val t1 = --`t1:bool`-- and t2 = --`t2:bool`--
    val conj = --`$/\`--   and disj = --`$\/`--
    val [NOT1,NOT2] = tl (CONJUNCTS NOT_CLAUSES)
    and [EQ1,EQ2,EQ3,EQ4] = map GEN_ALL (CONJUNCTS (SPEC_ALL EQ_CLAUSES))
    and [OR1,OR2,OR3,OR4,_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
    and [AND1,AND2,AND3,AND4,_] = map GEN_ALL (CONJUNCTS(SPEC_ALL AND_CLAUSES))
    val thTl = SPEC t2 EQ1
    and thFl = SPEC t2 EQ3
    val thTr = TRANS (MK_COMB (AP_TERM disj (SPEC t2 AND1),
                               TRANS (AP_THM (AP_TERM conj NOT1) (mk_neg t2))
                                     (SPEC (mk_neg t2) AND3)))
                     (SPEC t2 OR4)
    and thFr = TRANS (MK_COMB (AP_TERM disj (SPEC t2 AND3),
                               TRANS (AP_THM (AP_TERM conj NOT2) (mk_neg t2))
                                     (SPEC (mk_neg t2) AND1)))
                     (SPEC (mk_neg t2) OR3)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(t1 = t2) = ((t1 /\ t2) \/ (~t1 /\ ~t2))`--)
    val thT2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = T`--)] tm tm
    and thF2 = SUBST_CONV [t1 |-> ASSUME (--`t1 = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [t1,t2] (DISJ_CASES (SPEC t1 BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("EQ_EXPAND", EQ_EXPAND);

(* ---------------------------------------------------------------------*)
(* COND_RATOR |- !b (f:'a->'b) g x. (b => f | g) x = (b => f x | g x)   *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val COND_RATOR =
let val f = --`f: 'a -> 'b`--
    val g = --`g: 'a -> 'b`--
    val x = --`x:'a`--
    and b = --`b:bool`--
    val fx = --`^f ^x`-- and gx = --`^g ^x`--
    val t1 = --`t1:'a`--
    val t2 = --`t2:'a`--
    val theta1 = [Type`:'a` |-> Type`:'a -> 'b`]
    val theta2 = [Type`:'a` |-> Type`:'b`]
    val (COND_T,COND_F) = (GENL[t1,t2]##GENL[t1,t2])
                          (CONJ_PAIR(SPEC_ALL COND_CLAUSES))
    val thTl = AP_THM (SPECL [f,g] (INST_TYPE theta1 COND_T)) x
    and thFl = AP_THM (SPECL [f,g] (INST_TYPE theta1 COND_F)) x
    val thTr = SPECL [fx,gx] (INST_TYPE theta2 COND_T)
    and thFr = SPECL [fx,gx] (INST_TYPE theta2 COND_F)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(b => (f:'a->'b ) | g) x = (b => f x | g x)`--)
    val thT2 = SUBST_CONV [b |-> ASSUME (--`b = T`--)] tm tm
    and thF2 = SUBST_CONV [b |-> ASSUME (--`b = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
    GENL [b,f,g,x] (DISJ_CASES (SPEC b BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("COND_RATOR", COND_RATOR);

(* ---------------------------------------------------------------------*)
(* COND_RAND							        *)
(*								        *)
(* |- !(f:'a->'b) b x y. f (b => x | y) = (b => f x | f y)	        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val COND_RAND =
let val f = --`f: 'a -> 'b`--
    val x = --`x:'a`--
    val y = --`y:'a`--
    and b = --`b:bool`--
    val fx = --`^f ^x`-- and fy = --`^f ^y`--
    val t1 = --`t1:'a`--
    val t2 = --`t2:'a`--
    val theta = [Type`:'a` |-> Type`:'b`]
    val (COND_T,COND_F) = (GENL[t1,t2]##GENL[t1,t2])
                          (CONJ_PAIR (SPEC_ALL COND_CLAUSES))
    val thTl = AP_TERM f (SPECL [x,y] COND_T)
    and thFl = AP_TERM f (SPECL [x,y] COND_F)
    val thTr = SPECL [fx,fy] (INST_TYPE theta COND_T)
    and thFr = SPECL [fx,fy] (INST_TYPE theta COND_F)
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(f:'a->'b ) (b => x | y) = (b => f x | f y)`--)
    val thT2 = SUBST_CONV [b |-> ASSUME (--`b = T`--)] tm tm
    and thF2 = SUBST_CONV [b |-> ASSUME (--`b = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [f,b,x,y] (DISJ_CASES (SPEC b BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("COND_RAND", COND_RAND);

(* ---------------------------------------------------------------------*)
(* COND_ABS							        *)
(*								        *)
(* |- !b (f:'a->'b) g. (\x. (b => f(x) | g(x))) = (b => f | g)	        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val COND_ABS =
let val b = --`b:bool`--
    val f = --`f:'a->'b`--
    val g = --`g:'a->'b`--
    val x = --`x:'a`--
 in
   GENL [b,f,g]
      (TRANS (ABS x (SYM (SPECL [b,f,g,x] COND_RATOR)))
             (ETA_CONV (--`\^x. (^b => ^f | ^g) ^x`--)))
 end;

val _ = save_thm("COND_ABS", COND_ABS);

(* ---------------------------------------------------------------------*)
(* COND_EXPAND							        *)
(*								        *)
(* |- !b t1 t2. (b => t1 | t2) = ((~b \/ t1) /\ (b \/ t2))	        *)
(*								        *)
(*				       	                   RJB 92.09.26 *)
(* ---------------------------------------------------------------------*)

val COND_EXPAND =
let val b    = --`b:bool`--
    val t1   = --`t1:bool`--
    val t2   = --`t2:bool`--
    val conj = --`$/\`--
    val disj = --`$\/`--
    val theta = [Type`:'a` |-> Type.bool]
    val (COND_T,COND_F) =
      let val t1 = --`t1:'a`--  and  t2 = --`t2:'a`--
      in (GENL[t1,t2]##GENL[t1,t2]) (CONJ_PAIR(SPEC_ALL COND_CLAUSES))
      end
    and [NOT1,NOT2] = tl (CONJUNCTS NOT_CLAUSES)
    and [OR1,OR2,OR3,OR4,_] = map GEN_ALL (CONJUNCTS (SPEC_ALL OR_CLAUSES))
    and [AND1,AND2,AND3,AND4,_] = map GEN_ALL (CONJUNCTS(SPEC_ALL AND_CLAUSES))
    val thTl = SPECL [t1,t2] (INST_TYPE theta COND_T)
    and thFl = SPECL [t1,t2] (INST_TYPE theta COND_F)
    val thTr =
      let val th1 = TRANS (AP_THM (AP_TERM disj NOT1) t1) (SPEC t1 OR3)
          and th2 = SPEC t2 OR1
      in
         TRANS (MK_COMB (AP_TERM conj th1,th2)) (SPEC t1 AND2)
      end
    and thFr =
      let val th1 = TRANS (AP_THM (AP_TERM disj NOT2) t1) (SPEC t1 OR1)
          and th2 = SPEC t2 OR3
      in
        TRANS (MK_COMB (AP_TERM conj th1,th2)) (SPEC t2 AND1)
      end
    val thT1 = TRANS thTl (SYM thTr)
    and thF1 = TRANS thFl (SYM thFr)
    val tm = (--`(b => t1 | t2) = ((~b \/ t1) /\ (b \/ t2))`--)
    val thT2 = SUBST_CONV [b |-> ASSUME (--`b = T`--)] tm tm
    and thF2 = SUBST_CONV [b |-> ASSUME (--`b = F`--)] tm tm
    val thT3 = EQ_MP (SYM thT2) thT1
    and thF3 = EQ_MP (SYM thF2) thF1
 in
   GENL [b, t1, t2] (DISJ_CASES (SPEC b BOOL_CASES_AX) thT3 thF3)
 end;

val _ = save_thm("COND_EXPAND", COND_EXPAND);



(*---------------------------------------------------------------------------*
 * Used in basicHol90Lib.Type_def_support                                    *
 *---------------------------------------------------------------------------*)
val ABS_REP_THM =
   let val th1 = ASSUME (--`?rep:'b->'a. TYPE_DEFINITION P rep`--)
       and th2 = MK_EXISTS (SPEC (--`P:'a->bool`--) TYPE_DEFINITION)
       val def = EQ_MP th2 th1
       val asm = ASSUME (#Body(dest_exists(concl def)))
       val (asm1,asm2)  = CONJ_PAIR asm
       val rep_eq =
         let val th1 = DISCH (--`a:'b=a'`--)
                         (AP_TERM (--`rep:'b->'a`--) (ASSUME (--`a:'b=a'`--)))
         in IMP_ANTISYM_RULE (SPECL [(--`a:'b`--),(--`a':'b`--)] asm1) th1
         end
       val ABS = (--`\r:'a. @a:'b. r = rep a`--)
       val absd =  RIGHT_BETA (AP_THM (REFL ABS) (--`rep (a:'b):'a`--))
       val lem = SYM(SELECT_RULE(EXISTS ((--`?a':'b.a=a'`--),(--`a:'b`--))
                                        (REFL (--`a:'b`--))))
       val TH1 = GEN (--`a:'b`--)
                     (TRANS(TRANS absd (SELECT_EQ (--`a':'b`--) rep_eq)) lem)
       val t1 = SELECT_RULE(EQ_MP (SPEC (--`r:'a`--) asm2)
                                  (ASSUME (--`(P:'a->bool) r`--)))
       val absd2 =  RIGHT_BETA (AP_THM (REFL ABS) (--`r:'a`--))
       val v = mk_var{Name="v",Ty=type_of(rhs (concl absd2))}
       val {lhs=t1l,rhs=t1r} = dest_eq (concl t1)
       val rep = fst(strip_comb t1r)
       val template = mk_eq{lhs=t1l, rhs = mk_comb{Rator=rep,Rand=v}}
       val imp1 = DISCH (--`(P:'a->bool) r`--)
                    (SYM (SUBST [v |-> SYM absd2] template t1))
       val t2 = EXISTS ((--`?a:'b. r:'a = rep a`--), (--`^ABS r`--))
	               (SYM(ASSUME (--`rep(^ABS (r:'a):'b) = r`--)))
       val imp2 = DISCH (--`rep(^ABS (r:'a):'b) = r`--)
     		        (EQ_MP (SYM (SPEC (--`r:'a`--) asm2)) t2)
       val TH2 = GEN (--`r:'a`--) (IMP_ANTISYM_RULE imp1 imp2)
       val CTH = CONJ TH1 TH2
       val ath = subst [ABS |-> Term`abs:'a->'b`] (concl CTH)
       val eth1 = EXISTS ((--`?abs:'a->'b. ^ath`--), ABS) CTH
       val eth2 = EXISTS ((--`?rep:'b->'a. ^(concl eth1)`--),
                          (--`rep:'b->'a`--)) eth1
       val result = DISCH (concl th1) (CHOOSE ((--`rep:'b->'a`--),def) eth2)
   in
   GEN (--`P:'a->bool`--) result
   end;

val _ = save_thm("ABS_REP_THM", ABS_REP_THM);

val _ = export_theory();

end; (* boolScript *)
