(****************************************************************************)
(* FILE          : norm_convs.sml                                           *)
(* DESCRIPTION   : Conversions for rewriting with arithmetic theorems.      *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton, University of Cambridge                     *)
(* DATE          : 4th March 1991                                           *)
(*                                                                          *)
(* TRANSLATOR    : R.J.Boulton, University of Cambridge                     *)
(* DATE          : 5th February 1993                                        *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 19th August 1996                                         *)
(****************************************************************************)

structure DecisionNormConvs =
struct

local
  open HolKernel Parse basicHol90Lib
  infix THEN
  (* VERY important that these be local declarations as this file does
     not have a .sig file to hide the Type and Term values below, and
     we absolutely don't want them exported. *)
  val (Type,Term) = parse_from_grammars boolTheory.bool_grammars
  fun -- q x = Term q
  fun == q x = Type q
in
fun failwith function =
  raise HOL_ERR{origin_structure = "DecisionNormConvs",
                origin_function = function, message = ""};

(*==========================================================================*)
(* Conversions for rewriting Boolean terms                                  *)
(*==========================================================================*)

val IMP_NORM_CONV = REWR_CONV IMP_DISJ_THM;

val EQ_CONJ_NORM_CONV =
   REWR_CONV (prove (--`(x = y) = (~x \/ y) /\ (x \/ ~y)`--,
                     BOOL_CASES_TAC (--`x:bool`--) THEN
                     BOOL_CASES_TAC (--`y:bool`--) THEN
                     REWRITE_TAC []));

val EQ_DISJ_NORM_CONV = REWR_CONV EQ_EXPAND;

val COND_CONJ_NORM_CONV = REWR_CONV COND_EXPAND;

val COND_DISJ_NORM_CONV =
   REWR_CONV (prove (--`(if b then t1 else t2) = (b /\ t1) \/ (~b /\ t2)`--,
                     BOOL_CASES_TAC (--`b:bool`--) THEN REWRITE_TAC []));

val NOT_NOT_NORM_CONV = REWR_CONV (CONJUNCT1 NOT_CLAUSES);

val (NOT_CONJ_NORM_CONV,NOT_DISJ_NORM_CONV) =
   let val th = GSPEC DE_MORGAN_THM
   in  (REWR_CONV (CONJUNCT1 th),REWR_CONV (CONJUNCT2 th))
   end;

val NOT_IMP_NORM_CONV = REWR_CONV NOT_IMP;

val NOT_EQ_CONJ_NORM_CONV =
   REWR_CONV (prove (--`~(x = y) = (x \/ y) /\ (~x \/ ~y)`--,
                     BOOL_CASES_TAC (--`x:bool`--) THEN
                     BOOL_CASES_TAC (--`y:bool`--) THEN
                     REWRITE_TAC []));

val NOT_EQ_DISJ_NORM_CONV =
   REWR_CONV (prove (--`~(x = y) = (x /\ ~y) \/ (~x /\ y)`--,
                     BOOL_CASES_TAC (--`x:bool`--) THEN
                     BOOL_CASES_TAC (--`y:bool`--) THEN
                     REWRITE_TAC []));

val NOT_COND_CONJ_NORM_CONV =
   REWR_CONV (prove (--`~(if b then t1 else t2) = (~b \/ ~t1) /\ (b \/ ~t2)`--,
                     BOOL_CASES_TAC (--`b:bool`--) THEN REWRITE_TAC []));

val NOT_COND_DISJ_NORM_CONV =
   REWR_CONV (prove (--`~(if b then t1 else t2) = (b /\ ~t1) \/ (~b /\ ~t2)`--,
                     BOOL_CASES_TAC (--`b:bool`--) THEN REWRITE_TAC []));

val CONJ_ASSOC_NORM_CONV = REWR_CONV (GSYM CONJ_ASSOC);

val DISJ_ASSOC_NORM_CONV = REWR_CONV (GSYM DISJ_ASSOC);

val LEFT_CONJ_NORM_CONV = REWR_CONV LEFT_OR_OVER_AND;

val RIGHT_CONJ_NORM_CONV = REWR_CONV RIGHT_OR_OVER_AND;

val LEFT_DISJ_NORM_CONV = REWR_CONV LEFT_AND_OVER_OR;

val RIGHT_DISJ_NORM_CONV = REWR_CONV RIGHT_AND_OVER_OR;

val OR_F_CONV = REWR_CONV (el 3 (CONJUNCTS (SPEC (--`x:bool`--) OR_CLAUSES)));

val IMP_F_EQ_F_CONV = REWR_CONV IMP_F_EQ_F;

val IMP_IMP_CONJ_IMP_CONV = REWR_CONV AND_IMP_INTRO;

val X_AND_NOT_X_F_CONV =
   REWR_CONV (MATCH_MP (SPEC_ALL NOT_F) (SPEC_ALL NOT_AND));

val NOT_EQT_INTRO_CONV =
   REWR_CONV
      (AP_TERM (--`$~`--) (SYM (el 2 (CONJUNCTS (SPEC_ALL EQ_CLAUSES)))));

(*--------------------------------------------------------------------------*)
(* NOT_NOT_INTRO_CONV : conv                                                *)
(*                                                                          *)
(* `b`  --->  |- b = ~~b  provided b is of type ":bool".                    *)
(*--------------------------------------------------------------------------*)

val NOT_NOT_INTRO_CONV = SYM o NOT_NOT_NORM_CONV o mk_neg o mk_neg;

(*==========================================================================*)
(* Conversions for final simplification                                     *)
(*==========================================================================*)

val FORALL_SIMP_CONV = REWR_CONV FORALL_SIMP;

val EXISTS_SIMP_CONV = REWR_CONV EXISTS_SIMP;

(*==========================================================================*)
(* Conversions for normalising and eliminating conditionals                 *)
(*==========================================================================*)

val COND_RATOR_CONV = REWR_CONV COND_RATOR;
val COND_RAND_CONV = REWR_CONV COND_RAND;

end;  (* local *)


(*==========================================================================*)
(* Lazy rules                                                               *)
(*==========================================================================*)

local  open Exception Psyntax DecisionConv DecisionSupport LazyThm
       val aconv = Term.aconv
       val dest_neg = Dsyntax.dest_neg
       val mk_neg = Dsyntax.mk_neg
in

val NOT_EQT_INTRO =
   let fun not_eqt_intro conc = mk_neg (mk_eq (dest_neg conc,T))
   in  fn th =>
          (apply_rule1
              (apply_to_concl not_eqt_intro,CONV_RULE NOT_EQT_INTRO_CONV) th
           handle HOL_ERR _ => failwith "NOT_EQT_INTRO")
   end;

val IMP_F_EQ_F_RULE =
   let fun imp_f_eq_f conc =
          let val (t1,t2) = dest_imp conc
          in  if (is_F t2) then mk_eq (t1,F) else failwith ""
          end
   in  fn th =>
          (apply_rule1 (apply_to_concl imp_f_eq_f,CONV_RULE IMP_F_EQ_F_CONV) th
           handle HOL_ERR _ => failwith "IMP_F_EQ_F_RULE")
   end;

val IMP_IMP_CONJ_IMP_RULE =
   let fun imp_imp_conj_imp conc =
          let val (t1,t) = dest_imp conc
              val (t2,t3) = dest_imp t
          in  mk_imp (mk_conj (t1,t2),t3)
          end
   in  fn th => (apply_rule1 (apply_to_concl imp_imp_conj_imp,
                              CONV_RULE IMP_IMP_CONJ_IMP_CONV) th
                 handle HOL_ERR _ => failwith "IMP_IMP_CONJ_IMP_RULE")
   end;

val X_AND_NOT_X_F_RULE =
   let fun x_and_not_x_f conc =
          let val (t1,t2) = dest_conj conc
          in  if (aconv t1 (dest_neg t2)) then F else failwith ""
          end
   in  fn th => (apply_rule1 (apply_to_concl x_and_not_x_f,
                              CONV_RULE X_AND_NOT_X_F_CONV) th
                 handle HOL_ERR _ => failwith "X_AND_NOT_X_F_RULE")
   end;

end;

end; (* DecisionNormConvs *)
