structure ANF :> ANF =
struct

(* For interactive use:

 loadPath :=
            (concat Globals.HOLDIR "/examples/dev/sw") ::
            !loadPath;

app load ["pairLib", "cpsSyntax", "wordsLib"];
  quietdec := true;
  open pairLib pairTheory PairRules pairSyntax cpsTheory cpsSyntax;
  quietdec := false;
*)
open HolKernel Parse boolLib bossLib
     pairLib pairSyntax pairTheory PairRules cpsTheory cpsSyntax;

type env = (term * (bool * thm * thm * thm)) list;

val _ = (Globals.priming := SOME "");



(*---------------------------------------------------------------------------*)
(* Ensure that each let-bound variable name in a term is different than the  *)
(* others.                                                                   *)
(*---------------------------------------------------------------------------*)

fun std_bvars stem tm =
 let open Lib
     fun num2name i = stem^Lib.int_to_string i
     val nameStrm = Lib.mk_istream (fn x => x+1) 0 num2name
     fun next_name () = state(next nameStrm)
     fun trav M =
       if is_comb M then
            let val (M1,M2) = dest_comb M
                val M1' = trav M1
                val M2' = trav M2
            in mk_comb(M1',M2')
            end else
       if is_abs M then
           let val (v,N) = dest_abs(rename_bvar (next_name()) M)
           in mk_abs(v,trav N)
           end
       else M
 in
   trav tm
 end;

fun STD_BVARS_CONV stem tm =
 let val tm' = std_bvars stem tm
 in Thm.ALPHA tm tm'
 end;

val STD_BVARS = CONV_RULE o STD_BVARS_CONV;
val STD_BVARS_TAC = CONV_TAC o STD_BVARS_CONV;

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

val LET_SEQ_PAR_THM = Q.prove
(`!f1 f2 f3. Seq (Par f1 f2) f3 = \x. let v = f2 x in f3 (f1 x,v)`,
 RW_TAC std_ss [Seq_def, Par_def, LET_DEF]);

val SEQ_PAR_I_THM = Q.prove
(`!f2 f3. Seq (Par (\x.x) f2) f3 = \x. let v = f2 x in f3 (x,v)`,
 RW_TAC std_ss [LET_SEQ_PAR_THM,combinTheory.I_THM]);


fun is_word_literal tm =
  ((is_comb tm) andalso
  let val (c,args) = strip_comb tm
      val {Name,Thy,Ty} = dest_thy_const c
  in Name = "n2w" andalso numSyntax.is_numeral (hd args)
  end)
  handle HOL_ERR _ => raise ERR "is_word_literal" "";


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
  else if is_var t orelse is_word_literal t orelse numSyntax.is_numeral t orelse is_const t
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
  else if is_let t   (*  t = LET (\v. N) M  *)
   then let val (v,M,N) = dest_plet t
            val f1 = mk_pabs(args,args)
            val f2 = mk_pabs(args,M)
            val f3 = mk_pabs(mk_pair(args,v),N)
            val th1 = ISPECL [f1,f2,f3] LET_SEQ_PAR_THM
            val th2 = CONV_RULE(RHS_CONV(SIMP_CONV std_ss [LAMBDA_PROD])) th1
            val th3 = TRANS th2 (SYM (QCONV (SIMP_CONV std_ss [LAMBDA_PROD]) f))
            val th4 = SYM th3
        in
         if aconv (lhs(concl th4)) f
          then CONV_RULE
                (RHS_CONV
                  ((RAND_CONV Convert_CONV)
                   THENC (RATOR_CONV(RAND_CONV (RAND_CONV Convert_CONV)))))
                th4
          else (print "bad let case\n";
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
     val (func,args) = dest_comb l
     val is_recursive = Lib.can (find_term (aconv func)) r
(* val comb_exp_thm = if is_recursive then RecConvert def else Convert def *)
     val comb_exp_thm = Convert def
 in
   (is_recursive,lhs(concl comb_exp_thm), args, comb_exp_thm)
 end;

(*---------------------------------------------------------------------------*)
(* Takes theorem |- f = <combinator-form> , where f is not a recursive       *)
(* function, and returns the CPS-ed version of <combinator-form>. Actually,  *)
(* the returned value is in "A-Normal" form (uses lets).                     *)
(*---------------------------------------------------------------------------*)

val LET_ID = METIS_PROVE [] ``!f M. (LET M (\x. x)) = M (\x. x)``

fun REPAIR_SYNTAX_RESTRICTIONS_CONV t =
  if (is_comb t) then
    let
      val (f, args) = strip_comb t;
      val {Name,Thy,Ty} = dest_thy_const f;
    in
      if ((Name = "UNCURRY") andalso (Thy = "pair") andalso
          (length args = 2)) then
        let
          val pair = (el 2 args);
          val (l, r) = dest_pair pair;
          val is_word_l = is_word_literal l;
          val is_word_r = is_word_literal r;

          val _ = if (is_word_l andalso is_word_r) then
                     (raise (ERR "" "Can't repair syntax"))
                  else ()
        in
          if (is_word_l orelse is_word_r) then
            let
              val oper = el 1 args;
              val {Name,Thy,Ty} = dest_thy_const oper;

              val _ = if (not ((Thy="words") orelse (Name = "=" andalso (Thy="min")))) then
                        raise (ERR "" "Can't repair syntax")
                      else ()

              val _ = if ((Name = "word_mul")) then
                        raise (ERR "" "Can't repair syntax")
                      else ()


              fun COMM_OPER_CONV t =
                (CURRY_CONV THENC
                 ONCE_REWRITE_CONV [wordsTheory.WORD_ADD_COMM,
                                    wordsTheory.WORD_OR_COMM,
                                    wordsTheory.WORD_AND_COMM,
                                    wordsTheory.WORD_XOR_COMM,
                                    EQ_SYM_EQ
                                   ] THENC
                 UNCURRY_CONV) t
            in
              if (is_word_l) then
                if ((Name = "word_add") orelse
                    (Name = "word_or") orelse
                    (Name = "word_and") orelse
                    (Name = "word_xor") orelse
                    (Name = "=")) then
                  COMM_OPER_CONV t
                else
                  raise (ERR "" "Can't repair syntax")
              else REFL t
            end
          else
            REFL t
        end
      else
        (COMB_CONV REPAIR_SYNTAX_RESTRICTIONS_CONV) t
    end
  else if (is_abs t) then
      (ABS_CONV REPAIR_SYNTAX_RESTRICTIONS_CONV) t
  else
    REFL t;

fun VAR_LET_CONV t =
 let open pairSyntax
     val (_,tm) = dest_let t;
 in
   if is_vstruct tm orelse
      ((is_word_literal tm orelse numSyntax.is_numeral tm))

   then
      (REWR_CONV LET_THM THENC GEN_BETA_CONV THENC REPAIR_SYNTAX_RESTRICTIONS_CONV) t
   else raise ERR "VAR_LET_CONV" ""
 end;


fun ELIM_PAIR_LET_CONV t =
let
  val (body, value) = dest_let t;
in
   if (is_vstruct value) then
      (REWR_CONV LET_THM THENC GEN_BETA_CONV) t
   else
     let
      val thm = CURRY_CONV (liteLib.mk_icomb (body, value))
      val rhs_thm = rhs (concl thm);
      val (body, v1) = dest_comb rhs_thm
      val (body, v2) = dest_comb body
      val (varlist, body) = strip_pabs body;

      val body = mk_let (mk_pabs(el 2 varlist, body), v1);
      val body = mk_let (mk_pabs(el 1 varlist, body), v2);
      val thm = prove (mk_eq (t, body),
        CONV_TAC (DEPTH_CONV let_CONV) THEN REWRITE_TAC[])
    in
      thm
    end
end;


fun ANFof (args,thm) =
 let val thm1 = Q.AP_TERM `CPS` thm
     val thm2 = REWRITE_RULE [CPS_SEQ_INTRO, CPS_PAR_INTRO,(* CPS_REC_INTRO, *)
                                   CPS_ITE_INTRO] thm1
     val thm2a = REWRITE_RULE [CPS2_def] thm2
     val thm3 = CONV_RULE (DEPTH_CONV (REWR_CONV CPS_SEQ_def ORELSEC
                                       REWR_CONV CPS_PAR_def ORELSEC
                                       REWR_CONV CPS_ITE_def
(* ORELSEC REWR_CONV CPS_REC_def *))) thm2a
     val thm4 = CONV_RULE (DEPTH_CONV (REWR_CONV UNCPS)) thm3
     val thm5 = CONV_RULE (LAND_CONV (REWR_CONV CPS_def)) thm4
     val thm6 = CONV_RULE (REPEATC (STRIP_QUANT_CONV (HO_REWR_CONV FUN_EQ_THM)))
                          thm5
     val thm7 = BETA_RULE thm6
     val thm8 = BETA_RULE thm7
     val x = mk_var("x",fst (dom_rng (type_of (fst (dest_forall (concl thm8))))))
     val thm9 = ISPEC (mk_abs(x,x)) thm8
     val thm10 = SIMP_RULE bool_ss [LET_ID] thm9
     val thm11 = SIMP_RULE bool_ss [pairTheory.FORALL_PROD] thm10
     val thm12 = PBETA_RULE thm11
     val thm13 = SIMP_RULE bool_ss [pairTheory.LAMBDA_PROD] thm12
     val thm14 = PURE_REWRITE_RULE [FST,SND] thm13
     val thm15 = CONV_RULE (DEPTH_CONV ELIM_PAIR_LET_CONV) thm14
     val thm16 = STD_BVARS "v" thm15
     val thm17 = CONV_RULE (DEPTH_CONV VAR_LET_CONV) thm16
 in thm17
 end;


(*---------------------------------------------------------------------------*)
(* Given an environment and a possibly (tail) recursive definition, convert  *)
(* to combinator form, then to A-Normal form and add the result to the       *)
(* environment.                                                              *)
(*---------------------------------------------------------------------------*)
fun toANF env def =
 let val (is_recursive,func,args,const_eq_comb) = toComb def
     val anf = STD_BVARS "v" (ANFof (args,const_eq_comb))
 in
   (func,(is_recursive,def,anf,const_eq_comb))::env
 end;


end

