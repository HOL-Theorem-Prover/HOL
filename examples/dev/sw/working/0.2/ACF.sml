structure ACF  =
struct

local
open HolKernel Parse boolLib bossLib pairLib pairSyntax pairTheory PairRules ACFTheory;

in
(*---------------------------------------------------------------------------*)
(* Convert HOL programs to combinator-based pseudo-ASTs                      *)
(* Term programs is translated to equivalent A-Combinator Forms (ACF)        *)
(*---------------------------------------------------------------------------*)

val _ = (Globals.priming := SOME "");

(*---------------------------------------------------------------------------*)
(* Variable order defined for binary sets                                    *)
(*---------------------------------------------------------------------------*)

fun varOrder (t1:term, t2:term) =
  let val s1 = #1 (dest_var t1)
      val s2 = #1 (dest_var t2)
  in
  if s1 > s2 then GREATER
  else if s1 = s2 then EQUAL
  else LESS
  end;


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
(* Part of the Compiler frontend ... largely taken from ANF.sml              *)
(*---------------------------------------------------------------------------*)

(*****************************************************************************)
(* Error reporting function                                                  *)
(*****************************************************************************)

val ERR = mk_HOL_ERR "COMBINATOR";

(*****************************************************************************)
(* List of definitions (useful for rewriting)                                *)
(*****************************************************************************)

val SimpThms = [sc_def, cj_def, tr_def];

(*****************************************************************************)
(* An expression is just a HOL term built using expressions defined earlier  *)
(* in a program (see description of programs below) and sc, cj and tr:       *)
(*                                                                           *)
(*  expr := sc expr expr                                                     *)
(*        | cj expr expr expr                                                *)
(*        | tr expr expr expr                                                *)
(*                                                                           *)
(*****************************************************************************)

(*****************************************************************************)
(* to_combinator ``\(x1,...,xn). tm[x1,...,xn]`` returns a theorem           *)
(*                                                                           *)
(*  |- (\(x1,...,xn). tm[x1,...,xn]) = p                                     *)
(*                                                                           *)
(* where p is a combinatory expression built from the combinators            *)
(* sc and cj.                                                                *)
(*****************************************************************************)

fun is_word_literal tm =
  ((is_comb tm) andalso
  let val (c,args) = strip_comb tm
      val {Name,Thy,Ty} = dest_thy_const c
  in Name = "n2w" andalso numSyntax.is_numeral (hd args)
  end)
  handle HOL_ERR _ => raise ERR "is_word_literal" "";


fun to_combinator f =
 let val (args,t) = dest_pabs f
 in
   if is_var t orelse is_word_literal t orelse numSyntax.is_numeral t orelse is_const t orelse is_pair t then
     REFL f

   else if is_cond t then
     let val (b,t1,t2) = dest_cond t
            val fb = mk_pabs(args,b)
            val f1 = mk_pabs(args,t1)
            val f2 = mk_pabs(args,t2)
            val thb = PBETA_CONV (mk_comb(fb,args))
            val th1 = PBETA_CONV (mk_comb(f1,args))
            val th2 = PBETA_CONV (mk_comb(f2,args))
            val th3 = ISPECL [fb,f1,f2] cj_def
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
            CONV_RULE
                (RHS_CONV
                  ((RAND_CONV to_combinator)
                   THENC (RATOR_CONV(RAND_CONV to_combinator))
                   THENC (RATOR_CONV(RATOR_CONV(RAND_CONV to_combinator)))))
                th6
        end

  else if is_let t then  (*  t = LET (\v. N) M  *)
      let val (v,M,N) = dest_plet t
            val liveVarS = Binaryset.addList (Binaryset.empty varOrder, free_vars N)
            val extraVarS = Binaryset.delete (liveVarS, v)
            val th1 =
              if Binaryset.isEmpty extraVarS then
                let val f1 = mk_pabs(args, M)
                    val f2 = mk_pabs(v, N)
                in
                    ISPECL [f1,f2] sc_def
                end
              else
                let
                  val extraVars = list_mk_pair (Binaryset.listItems extraVarS)
                  val args1 = mk_pair (extraVars,v)
                  val f1 = mk_pabs(args, mk_pair (extraVars, M))
                  val f2 = mk_pabs(args1,N)
                in
                  ISPECL [f1,f2] sc_def
                end
              val th2 = CONV_RULE(RHS_CONV(SIMP_CONV std_ss [LAMBDA_PROD])) th1
              val th3 = TRANS th2 (SYM (QCONV (fn t => SIMP_CONV std_ss [LAMBDA_PROD, Once LET_THM] t) f))
              val th4 = SYM th3
        in
              CONV_RULE
                (RHS_CONV
                  ((RAND_CONV to_combinator)
                   THENC (RATOR_CONV (RAND_CONV (RAND_CONV to_combinator)))))
                th4
        end

  else if is_comb t then
       REFL f
  else
       REFL f
(*
  else (print_term f; print "\n";
        print "shouldn't get this case (not first-order)!\n";
        raise ERR "to_combinator" "shouldn't happen")
*)
 end;

(*****************************************************************************)
(* Predicate to test whether a term occurs in another term                   *)
(*****************************************************************************)

fun occurs_in t1 t2 = can (find_term (aconv t1)) t2;

(*****************************************************************************)
(* convert_to_combinator (|- f x = e) returns a theorem                      *)
(*                                                                           *)
(*  |- f = p                                                                 *)
(*                                                                           *)
(* where p is a combinatory expression built from the combinators Seq and Ite*)
(*****************************************************************************)

fun convert defth =
 let val (lt,rt) =
         dest_eq(concl(SPEC_ALL defth))
         handle HOL_ERR _
         => (print "not an equation\n"; raise ERR "Convert" "not an equation")
     val (func,args) =
         dest_comb lt
         handle HOL_ERR _ =>
         (print "lhs not a comb\n"; raise ERR "Convert" "lhs not a comb")
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
      val th1 = to_combinator f
      val th2 = PABS args (SPEC_ALL defth)
      val th3 = TRANS th2 th1
  in
   CONV_RULE (LHS_CONV PETA_CONV) th3
  end
 end;


(*****************************************************************************)
(* tr_convert (|- f x = if f1 x then f2 x else f(f3 x))                      *)
(*            (|- TOTAL(f1,f2,f3))                                           *)
(*                                                                           *)
(* returns a theorem                                                         *)
(*                                                                           *)
(*  |- f = tr (p1,p2,p3)                                                     *)
(*                                                                           *)
(* where p1, p2 and p3 are combinatory expressions built from the            *)
(* combinators sc and cj                                                     *)
(*                                                                           *)
(*****************************************************************************)


val I_DEF_ALT = Q.prove(`I = \x.x`,SIMP_TAC std_ss [FUN_EQ_THM]);
val rec_INTRO_ALT = REWRITE_RULE[I_DEF_ALT] rec_INTRO;
val sc_o = Q.prove(`!f g. f o g = sc g f`,
         SIMP_TAC std_ss [combinTheory.o_DEF,sc_def]);

(* Define `f1 (x,a) = if x = 0 then x + a else f1(x - 1, a * x)` *)

fun rec_convert defth =
 let val (lt,rt) = dest_eq(concl(SPEC_ALL defth))
     val (func,args) = dest_comb lt
     val (b,t1,t2) = dest_cond rt
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
       val thm = ISPECL[func,fb,f1,f2] rec_INTRO

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
                   (RAND_CONV to_combinator THENC
                    RATOR_CONV(RAND_CONV (RAND_CONV to_combinator)) THENC
                    RATOR_CONV(RAND_CONV (RATOR_CONV (RAND_CONV to_combinator)))))
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
(* by calling convert or tr_convert.                                         *)
(*---------------------------------------------------------------------------*)

fun toComb def =
 let val (l,r) = dest_eq(snd(strip_forall(concl def)))
     val (func,args) = dest_comb l
     val is_recursive = Lib.can (find_term (aconv func)) r
     val comb_exp_thm = if is_recursive then rec_convert def else convert def
 in
   (is_recursive,lhs(concl comb_exp_thm), args, comb_exp_thm)
 end;

(*---------------------------------------------------------------------------*)
(* Given an environment and a possibly (tail) recursive definition, convert  *)
(* to combinator form, then add the result to the environment.               *)
(*---------------------------------------------------------------------------*)

fun toACF env def =
 let val (is_recursive,func,args,const_eq_comb) = toComb def
 in
   (func,(is_recursive,def,const_eq_comb))::env
 end;


end
end
