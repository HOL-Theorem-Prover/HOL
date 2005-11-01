structure ANF :> ANF = 
struct

(* For interactive use:
 app load ["pairLib", "cpsSyntax"]; 
  quietdec := true;
  open pairLib pairTheory PairRules cpsTheory cpsSyntax; 
  quietdec := false;
*)
open HolKernel Parse boolLib bossLib 
     pairLib pairTheory PairRules cpsTheory cpsSyntax;

type env = (term * (bool * thm * thm * thm)) list;

val _ = (Globals.priming := SOME "");


(*---------------------------------------------------------------------------*)
(* Compiler frontend ... largely pinched from examples/dev/compile.sml       *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* Error reporting function                                                  *)
(*****************************************************************************)

val ERR = mk_HOL_ERR "ANF";

(*****************************************************************************)
(* List of definitions (useful for rewriting)                                *)
(*****************************************************************************)

val SimpThms = [Seq_def,Par_def,Ite_def,Rec_def];

(*****************************************************************************)
(* An expression is just a HOL term built using expressions defined earlier  *)
(* in a program (see description of programs below) and Seq, Par,            *)
(* Ite and Rec:                                                              *)
(*                                                                           *)
(*  expr := Seq expr expr                                                    *)
(*        | Par expr expr                                                    *)
(*        | Ite expr expr expr                                               *)
(*        | Rec expr expr expr                                               *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* Convert_CONV ``\(x1,...,xn). tm[x1,...,xn]`` returns a theorem            *)
(*                                                                           *)
(*  |- (\(x1,...,xn). tm[x1,...,xn]) = p                                     *)
(*                                                                           *)
(* where p is a combinatory expression built from the combinators            *)
(* Seq, Par and Ite. An example is:                                          *)
(*                                                                           *)
(*  - Convert_CONV ``\(x,y). if x < y then y-x else x-y``;                   *)
(* > val it =                                                                *)
(*     |- (\(x,y). (if x < y then y - x else x - y)) =                       *)
(*        Ite (Seq (Par (\(x,y). x) (\(x,y). y)) (UNCURRY $<))               *)
(*            (Seq (Par (\(x,y). y) (\(x,y). x)) (UNCURRY $-))               *)
(*            (Seq (Par (\(x,y). x) (\(x,y). y)) (UNCURRY $-))               *)
(*                                                                           *)
(* Notice that curried operators are uncurried.                              *)
(*                                                                           *)
(*****************************************************************************)

fun Convert_CONV f =
 let val (args,t) = 
         dest_pabs f
         handle HOL_ERR _
          => (print_term f; print"\n";
              print "is not an abstraction\n";
              raise ERR "Convert_CONV" "not an abstraction")
  in
  if not(free_vars f = []) 
  then (print_term f; print "\n";
        print "has free variables: "; 
        map (fn t => (print_term t; print " "))(rev(free_vars f)); print "\n";
        raise ERR "Convert_CONV" "disallowed free variables")
  else if null(free_vars t) orelse is_var t
   then REFL f
  else if is_pair t
   then let val (t1,t2) = dest_pair t
            val f1 = mk_pabs(args,t1)
            val f2 = mk_pabs(args,t2)
            val th1 = PBETA_CONV (mk_comb(f1,args))
            val th2 = PBETA_CONV (mk_comb(f2,args))
            val th3 = ISPECL [f1,f2] Par_def
            val ptm = mk_pabs(args, mk_pair(mk_comb(f1,args),mk_comb(f2,args))) 
            val th4 = TRANS th3 (PALPHA  (rhs(concl th3)) ptm)
            val th5 = CONV_RULE
                       (RHS_CONV
                         (PABS_CONV
                           (RAND_CONV(REWR_CONV th2)
                             THENC RATOR_CONV(RAND_CONV(REWR_CONV th1)))))
                       th4
            val th6 = GSYM th5
        in
         if aconv (lhs(concl th6)) f 
          then CONV_RULE
                (RHS_CONV 
                  ((RAND_CONV Convert_CONV) 
                   THENC (RATOR_CONV(RAND_CONV Convert_CONV))))
                th6
          else (print "bad Par case\n"; 
                raise ERR "Convert_CONV" "shouldn't happen")
        end
  else if is_cond t
   then let val (b,t1,t2) = dest_cond t
            val fb = mk_pabs(args,b)
            val f1 = mk_pabs(args,t1)
            val f2 = mk_pabs(args,t2)
            val thb = PBETA_CONV (mk_comb(fb,args))
            val th1 = PBETA_CONV (mk_comb(f1,args))
            val th2 = PBETA_CONV (mk_comb(f2,args))
            val th3 = ISPECL [fb,f1,f2] Ite_def
            val ptm = mk_pabs
                       (args,
                        mk_cond(mk_comb(fb,args),mk_comb(f1,args),mk_comb(f2,args))) 
            val th4 = TRANS th3 (PALPHA  (rhs(concl th3)) ptm)
            val th5 = CONV_RULE
                       (RHS_CONV
                         (PABS_CONV
                           (RAND_CONV(REWR_CONV th2)
                             THENC RATOR_CONV(RAND_CONV(REWR_CONV th1))
                             THENC RATOR_CONV(RATOR_CONV(RAND_CONV(REWR_CONV thb))))))
                       th4
            val th6 = GSYM th5
        in
         if aconv (lhs(concl th6)) f 
          then CONV_RULE
                (RHS_CONV 
                  ((RAND_CONV Convert_CONV) 
                   THENC (RATOR_CONV(RAND_CONV Convert_CONV))
                   THENC (RATOR_CONV(RATOR_CONV(RAND_CONV Convert_CONV)))))
                th6
          else (print "bad Ite case\n"; 
                raise ERR "Convert_CONV" "shouldn't happen")
        end
  else if is_comb t 
   then let val th0 = (REWR_CONV (GSYM UNCURRY_DEF) ORELSEC REFL) t
            val (t1,t2) = dest_comb(rhs(concl th0))
            val f1 = mk_pabs(args,t1)
            val f2 = mk_pabs(args,t2)
            val th1 = ISPECL [f2,t1] Seq_def
            val ptm = mk_pabs(args, mk_comb(t1,mk_comb(f2,args)))
            val th2 = TRANS th1 (PALPHA (rhs(concl th1)) ptm)
            val th3 = PBETA_CONV(mk_comb(f2,args))
            val th4 = GSYM(CONV_RULE(RHS_CONV(PABS_CONV(RAND_CONV(REWR_CONV th3))))th2)
            val th5 = CONV_RULE(LHS_CONV(PABS_CONV(REWR_CONV(GSYM th0)))) th4
        in
         if aconv (lhs(concl th5)) f 
          then CONV_RULE
                (RHS_CONV 
                  (RATOR_CONV(RAND_CONV Convert_CONV)))
                th5
          else (print "bad Seq case\n"; 
                raise ERR "Convert_CONV" "shouldn't happen")
        end
  else (print_term f; print "\n";
        print "shouldn't get this case (not first-order)!\n";
        raise ERR "Convert_CONV" "shouldn't happen")
 end;

(*****************************************************************************)
(* Predicate to test whether a term occurs in another term                   *)
(*****************************************************************************)

fun occurs_in t1 t2 = can (find_term (aconv t1)) t2;

(*****************************************************************************)
(* Convert (|- f x = e) returns a theorem                                    *)
(*                                                                           *)
(*  |- f = p                                                                 *)
(*                                                                           *)
(* where p is a combinatory expression built from the combinators Seq, Par   *)
(* and Ite.                                                                  *)
(*****************************************************************************)

fun Convert defth =
 let val (lt,rt) = 
         dest_eq(concl(SPEC_ALL defth))
         handle HOL_ERR _ 
         => (print "not an equation\n"; 
             raise ERR "Convert" "not an equation")
     val (func,args) = 
         dest_comb lt
         handle HOL_ERR _ => 
         (print "lhs not a comb\n"; 
          raise ERR "Convert" "lhs not a comb")
     val _ = if not(is_const func)
              then (print_term func; print " is not a constant\n";
                    raise ERR "Convert" "rator of lhs not a constant")
              else ()
     val _ = if not(subtract (free_vars rt) (free_vars lt) = [])
              then (print "definition rhs has unbound variables: "; 
                    map (fn t => (print_term t; print " "))
                        (rev(subtract (free_vars rt) (free_vars lt))); 
                    print "\n";
                    raise ERR "Convert" "definition rhs has unbound variables")
              else ()
 in
  let val f = mk_pabs(args,rt)
      val th1 = Convert_CONV f
      val th2 = PABS args (SPEC_ALL defth)
      val th3 = TRANS th2 th1
  in
   CONV_RULE (LHS_CONV PETA_CONV) th3
  end
 end;


(*****************************************************************************)
(* RecConvert (|- f x = if f1 x then f2 x else f(f3 x))                      *)
(*            (|- TOTAL(f1,f2,f3))                                           *)
(*                                                                           *)
(* returns a theorem                                                         *)
(*                                                                           *)
(*  |- f = Rec(p1,p2,p3)                                                     *)
(*                                                                           *)
(* where p1, p2 and p3 are combinatory expressions built from the            *)
(* combinators Seq, Par and Ite.                                             *)
(*                                                                           *)
(* For example, given:                                                       *)
(*                                                                           *)
(*  FactIter;                                                                *)
(*  > val it =                                                               *)
(*      |- FactIter (n,acc) =                                                *)
(*         (if n = 0 then (n,acc) else FactIter (n - 1,n * acc))             *)
(*                                                                           *)
(*  - FactIter_TOTAL;                                                        *)
(*  > val it =                                                               *)
(*      |- TOTAL                                                             *)
(*           ((\(n,acc). n = 0),                                             *)
(*            (\(n,acc). (n,acc)),                                           *)
(*            (\(n,acc). (n-1, n*acc)))                                      *)
(*                                                                           *)
(* then:                                                                     *)
(*                                                                           *)
(*  - RecConvert FactIter FactIter_TOTAL;                                    *)
(* > val it =                                                                *)
(*     |- FactIter =                                                         *)
(*        Rec (Seq (Par (\(n,acc). n) (\(n,acc). 0)) (UNCURRY $=))           *)
(*            (Par (\(n,acc). n) (\(n,acc). acc))                            *)
(*            (Par (Seq (Par (\(n,acc). n) (\(n,acc). 1)) (UNCURRY $-))      *)
(*                (Seq (Par (\(n,acc). n) (\(n,acc). acc)) (UNCURRY $* )))   *)
(*                                                                           *)
(*****************************************************************************)

val I_DEF_ALT = Q.prove(`I = \x.x`,SIMP_TAC std_ss [FUN_EQ_THM]);
val Rec_INTRO_ALT = REWRITE_RULE[I_DEF_ALT] Rec_INTRO;
val Seq_o = Q.prove(`!f g. f o g = Seq g f`,
         SIMP_TAC std_ss [combinTheory.o_DEF,Seq_def]);

fun RecConvert defth =
 let val (lt,rt) = 
         dest_eq(concl(SPEC_ALL defth))
         handle HOL_ERR _ 
         => (print "not an equation\n"; 
             raise ERR "RecConvert" "not an equation")
     val (func,args) = 
         dest_comb lt
         handle HOL_ERR _ => 
         (print "lhs not a comb\n"; 
          raise ERR "RecConvert" "lhs not a comb")
     val _ = if not(is_const func)
              then (print_term func; print " is not a constant\n";
                    raise ERR "RecConvert" "rator of lhs not a constant")
              else ()
     val (b,t1,t2) = 
         dest_cond rt
         handle HOL_ERR _ 
         => (print "rhs not a conditional\n"; 
             raise ERR "RecConvert" "rhs not a conditional")
     val _ = if not(subtract (free_vars rt) (free_vars lt) = [])
              then (print "definition rhs has unbound variables: "; 
                    map (fn t => (print_term t; print " "))
                        (rev(subtract (free_vars rt) (free_vars lt))); 
                    print "\n";
                    raise ERR "RecConvert" "definition rhs has unbound variables")
              else()
 in
  if (is_comb t2 
       andalso aconv (rator t2) func
       andalso not(occurs_in func b)
       andalso not(occurs_in func t1)
       andalso not(occurs_in func (rand t2)))
  then 
   let val fb = mk_pabs(args,b)
       val f1 = mk_pabs(args,t1)
       val f2 = mk_pabs(args,rand t2)
       val thm = ISPECL[func,fb,f1,f2] Rec_INTRO
       val M = fst(dest_imp(concl thm))
       val (v,body) = dest_forall M
       val M' = rhs(concl(DEPTH_CONV PBETA_CONV 
                 (mk_pforall(args,subst [v |-> args]body))))
       val MeqM' = prove(mk_eq(M,M'),
                    Ho_Rewrite.REWRITE_TAC[LAMBDA_PROD]
                     THEN PBETA_TAC THEN REFL_TAC)
       val thm1 = PURE_REWRITE_RULE[MeqM'] thm
       val thm2 = PGEN args defth
       val thm3 = MP thm1 thm2
       val N = fst(dest_imp(concl thm3))
       val (R,tm) = dest_exists N
       val (tm1,tm2) = dest_conj tm
       val (v,body) = dest_forall tm2
       val tm2' = rhs(concl(DEPTH_CONV PBETA_CONV 
                 (mk_pforall(args,subst [v |-> args]body))))
       val N' = mk_exists(R,mk_conj(tm1,tm2'))
       val NeqN' = prove(mk_eq(N,N'),
                    Ho_Rewrite.REWRITE_TAC[LAMBDA_PROD]
                     THEN PBETA_TAC THEN REFL_TAC)
       val thm4 = PURE_REWRITE_RULE[NeqN'] thm3
       val thm5 = UNDISCH thm4
       val thm6 = CONV_RULE (RHS_CONV
                   (RAND_CONV Convert_CONV THENC
                    RATOR_CONV(RAND_CONV Convert_CONV) THENC
                    RATOR_CONV(RATOR_CONV(RAND_CONV Convert_CONV))))
                  thm5
    in thm6
    end
  else if occurs_in func rt
   then (print "definition of: "; print_term func; 
         print " is not tail recursive"; print "\n";
         raise ERR "RecConvert" "not tail recursive")
   else raise ERR "RecConvert" "this shouldn't happen"
 end;

(*---------------------------------------------------------------------------*)
(* Convert a possibly (tail) recursive equation to combinator form, either   *)
(* by calling Convert or RecConvert.                                         *)
(*---------------------------------------------------------------------------*)

fun toComb def = 
 let val (l,r) = dest_eq(snd(strip_forall(concl def)))
     val (func,_) = strip_comb l
     val is_recursive = Lib.can (find_term (aconv func)) r
     val comb_exp_thm = if is_recursive then RecConvert def else Convert def
 in 
   (is_recursive,lhs(concl comb_exp_thm), comb_exp_thm)
 end;

(*---------------------------------------------------------------------------*)
(* Takes theorem |- f = <combinator-form> , where f is not a recursive       *)
(* function, and returns the CPS-ed version of <combinator-form>. Actually,  *)
(* the returned value is in "A-Normal" form (uses lets).                     *)
(*---------------------------------------------------------------------------*)

val LET_ID = METIS_PROVE [] ``!f M. (LET M (\x. x)) = M (\x. x)``

fun ANFof thm =
 let val thm1 = Q.AP_TERM `CPS` thm
     val thm2 = REWRITE_RULE [CPS_SEQ_INTRO, CPS_PAR_INTRO,CPS_REC_INTRO,
                                   CPS_ITE_INTRO] thm1
     val thm3 = CONV_RULE (DEPTH_CONV (REWR_CONV CPS_SEQ_def ORELSEC
                                       REWR_CONV CPS_PAR_def ORELSEC
                                       REWR_CONV CPS_ITE_def ORELSEC
                                       REWR_CONV CPS_REC_def)) thm2 
     val thm4 = CONV_RULE (DEPTH_CONV (REWR_CONV UNCPS)) thm3
     val thm5 = CONV_RULE (LAND_CONV (REWR_CONV CPS_def)) thm4
     val thm6 = CONV_RULE (REPEATC (STRIP_QUANT_CONV (HO_REWR_CONV FUN_EQ_THM)))
                          thm5
     val thm7 = BETA_RULE thm6
     val thm8 = BETA_RULE thm7
     val thm9 = Q.ISPEC `\x:^(ty_antiq (fst (dom_rng (type_of (fst (dest_forall (concl thm8))))))).x` thm8
     val thm10 = SIMP_RULE bool_ss [LET_ID] thm9
     (* Generating thm11 takes about half the time on TEA's Round function *)
     val thm11 = SIMP_RULE bool_ss [pairTheory.FORALL_PROD] thm10
     val thm12 = PBETA_RULE thm11
 in thm12
 end;

(*---------------------------------------------------------------------------*)
(* Takes theorem |- f = <combinator-form> , where f is a recursive function, *)
(* and returns the ANF'ed version of <combinator-form>.                      *)
(* Much re-use of code from nonRec_to_ANF. Mostly, the new code just arranges*)
(* to use the hypothesis of thm (termination conditions) to prove the        *)
(* antecedent of CPS_REC_INTRO so that it can be applied. This allows Rec to *)
(* replaced by CPS_REC. In order to get rid of CPS_REC, by rewriting with    *)
(* CPS_REC_THM, something similar has to be done.                            *)
(*---------------------------------------------------------------------------*)
(*
fun Rec_to_ANF thm =
 let val (f1,f2) = dest_seq (rhs (concl thm))
     val args = fst(dest_pabs f2)
     val (e,f,g) = dest_rec f1
     val CPS_REC_INTRO1 = ISPECL [e,f,g] CPS_REC_INTRO
     val N = fst(dest_imp(concl CPS_REC_INTRO1))
     val (R,tm) = dest_exists N
     val (tm1,tm2) = dest_conj tm
     val (v,body) = dest_forall tm2
     val tm2' = rhs(concl
                  (SIMP_CONV std_ss [Seq_def,Par_def,Ite_def]
                    (mk_pforall(args,subst [v |-> args]body))))
     val N' = mk_exists(R,mk_conj(tm1,tm2'))
     val NeqN' = prove(mk_eq(N,N'),
                    SIMP_TAC std_ss [LAMBDA_PROD,Seq_def,Par_def,Ite_def])
     val CPS_REC_INTRO2 = PURE_REWRITE_RULE[NeqN'] CPS_REC_INTRO1
     val CPS_REC_INTRO3 = MATCH_MP CPS_REC_INTRO2 (ASSUME (hd(hyp thm)))
     val thm1 = Q.AP_TERM `CPS` thm
     val thm2 = SIMP_RULE bool_ss [CPS_SEQ_INTRO, CPS_PAR_INTRO,
                                   CPS_ITE_INTRO,CPS2_INTRO,
                                   CPS_REC_INTRO3] thm1
     val thm3 = SIMP_RULE bool_ss [CPS_SEQ_def, CPS_PAR_def, CPS_ITE_def] thm2
     val thm4 = SIMP_RULE bool_ss [UNCPS] thm3
     val thm5 = SIMP_RULE bool_ss [CPS_def, FUN_EQ_THM, CPS_TEST_def] thm4
     val thm6 = CONV_RULE (DEPTH_CONV ((HO_REWR_CONV MY_LET_RAND) ORELSEC
                          (HO_REWR_CONV (GSYM COND_RAND)) ORELSEC
                          (HO_REWR_CONV UNLET))) thm5
     val x = mk_var("x",fst (dom_rng 
                         (type_of (fst (dest_forall (concl thm6))))))
     val thm7 = ISPEC (mk_abs(x,x)) thm6
     val thm8 = SIMP_RULE bool_ss [pairTheory.FORALL_PROD] thm7
     val thm9 = PBETA_RULE thm8
 in thm9
 end;
*)

(*---------------------------------------------------------------------------*)
(* Given an environment and a possibly (tail) recursive definition, convert  *)
(* to combinator form, then to A-Normal form and add the result to the       *)
(* environment.                                                              *)
(*---------------------------------------------------------------------------*)

fun toANF env def = 
 let val (is_recursive,func,const_eq_comb) = toComb def
     val anf = ANFof const_eq_comb
 in 
   (func,(is_recursive,def,anf,const_eq_comb))::env
 end;

end
