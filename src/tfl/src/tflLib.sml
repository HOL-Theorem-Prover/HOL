(*---------------------------------------------------------------------------*
 * Some convenient specializations of TFL primitives. Makes the assumption   *
 * that we are working over a base of at least pairs, nums, and lists. This  *
 * is accomplished via the use of Datatype.theTypeBase.                      *
 *---------------------------------------------------------------------------*)
structure tflLib :> tflLib = 
struct

open HolKernel Parse basicHol90Lib Let_conv boolTheory NonRecSize;

infix THEN ORELSE; infixr -->;

val output = Portable.output
val std_out = Portable.std_out
val flush_out = Portable.flush_out

val _ = RW.add_implicit_congs [boolTheory.IMP_CONG,boolTheory.COND_CONG];
val _ = RW.add_implicit_rws pairTheory.pair_rws;

type term = Term.term
type thm =  Thm.thm
type tactic = Abbrev.tactic

val timing = ref false;

fun TFL_LIB_ERR func mesg = 
     HOL_ERR{origin_structure="tflLib",origin_function=func,message=mesg};

(*---------------------------------------------------------------------------*
 * The current notion of context used by Tfl. Context is represented via     *
 * congruence rules. This is extensible via Tfl.write_context (and making    *
 * Hol_datatype declarations).                                               *
 *---------------------------------------------------------------------------*)
fun current_congs() = 
   Tfl.read_context() 
   @
   rev_itlist (fn db => fn C => (TypeBase.case_cong_of db::C))
             (TypeBase.listItems (TypeBase.theTypeBase())) [] ;


fun timer s1 f s2 =
   let open Portable
   in if !timing 
      then let val _ = output(std_out, s1)
               val _ = flush_out std_out
               val x = Lib.time f ()
               val _ = output(std_out, s2) 
               val _ = flush_out std_out
            in x end
       else f()
   end;

(*---------------------------------------------------------------------------*
 * Support for curried functions.                                            *
 *---------------------------------------------------------------------------*)
val prod_tyl = 
  end_itlist(fn ty1 => fn ty2 => mk_type{Tyop="prod",Args=[ty1,ty2]});

fun variants FV vlist = 
  rev(fst (rev_itlist (fn v => fn (V,W) => 
             let val v' = variant W v in (v'::V, v'::W) end)
             vlist ([],FV)));

fun drop [] x = x
  | drop (_::t) (_::rst) = drop t rst
  | drop _ _ = raise TFL_LIB_ERR "drop" "second list empty";

(*---------------------------------------------------------------------------*
 * On entry to this, we know that f is curried, i.e., of type                *
 *                                                                           *
 *    f : ty1 -> ... -> tyn -> rangety                                       *
 *                                                                           *
 *---------------------------------------------------------------------------*)
fun pairf (f,name,argtys,range_ty,eqs0) =
 let val unc_argty = prod_tyl argtys
     val f' = Lib.with_flag (Globals.priming, SOME"")
              mk_primed_var
                {Name=if Lexis.ok_identifier name
                      then "tfl_unc_"^name else "tfl_unc",
                 Ty = unc_argty --> range_ty}
     fun rebuild tm = 
      case (dest_term tm)
      of COMB _ => 
         let val (g,args) = strip_comb tm
             val args' = map rebuild args
         in if (g=f) 
            then if length args < length argtys  (* partial application *)
                 then let val newvars = map (fn ty => mk_var{Name="a", Ty=ty})
                                            (drop args argtys)
                          val newvars' = variants (free_varsl args') newvars
                      in list_mk_abs(newvars', 
                          mk_comb{Rator=f',Rand=list_mk_pair(args' @newvars')})
                      end
                 else mk_comb{Rator=f', Rand=list_mk_pair args'}
            else list_mk_comb(g,args')
         end
       | LAMB{Bvar,Body} => mk_abs{Bvar=Bvar, Body=rebuild Body}
       | _ => tm
 in 
    rebuild eqs0
 end;


(*---------------------------------------------------------------------------*
 * Find the name of a to-be-defined constant from a quotation. Or at         *
 * least try to.                                                             *
 *---------------------------------------------------------------------------*)

fun alphabetic c   = Lexis.in_class(Lexis.alphabet,      Char.ord c);
fun alphanumeric c = Lexis.in_class(Lexis.alphanumerics, Char.ord c);
fun symbolic c     = Lexis.in_class(Lexis.hol_symbols,   Char.ord c);
fun starts_ident c = alphanumeric c orelse symbolic c ;

fun grab_first_ident s =
 let val ss0 = Substring.dropl (not o starts_ident) (Substring.all s)
     val ident_ss =
       case Substring.getc ss0
        of NONE => raise TFL_LIB_ERR "grab_first_ident" "can't find an ident"
         | SOME(c,_) => 
             if (symbolic c) 
             then Substring.takel symbolic ss0
             else if (alphabetic c) 
                  then Substring.takel alphanumeric ss0
                  else raise TFL_LIB_ERR "grab_first_ident" 
                           "can't find an ident.1"
 in 
   Substring.string ident_ss
 end;

local (* this is dodgy - shouldn't it loop? *)
      fun strip_imp tm = if is_neg tm then ([],tm) else strip_imp tm
in
fun termination_goals rules = 
 itlist (fn th => fn A =>
           let val tcl = (fst o strip_imp o #2 o strip_forall o concl) th
           in tcl@A
           end) (CONJUNCTS rules) (hyp rules)
end;

(*---------------------------------------------------------------------------*
 * "rfunction" is one of the main entrypoints to the definition mechanisms.  *
 * "rfunction" is not for normal use, only for when "Rfunction" is not       *
 * satisfactory. "rfunction" is parameterized by a postprocessor and yet     *
 * another simplifier ("reducer"). This reducer attempts to eliminate        *
 * (or simplify, when that's not possible) solved termination conditions,    *
 * in the definition and induction theorems. This reducer is only invoked    *
 * on the results of defining a nested recursion.                            *
 *---------------------------------------------------------------------------*)
local fun id_thm th = 
       let val {lhs,rhs} = dest_eq(#2(strip_forall(concl th)))
       in aconv lhs rhs
       end handle HOL_ERR _ => false
    val solved = not o can dest_eq o #2 o strip_forall o concl
    fun join_assums th = 
       let val {lhs,rhs} = dest_eq(#2 (strip_forall (concl th)))
           val cntxtl = (#1 o strip_imp) lhs  (* cntxtl should be cntxtr *)
           val cntxtr = (#1 o strip_imp) rhs  (* but this way is solider *)
           val cntxt = op_union aconv cntxtl cntxtr
       in 
       GEN_ALL(DISCH_ALL(Rewrite.REWRITE_RULE(map ASSUME cntxt) (SPEC_ALL th)))
       end
    val gen_all = tflUtils.gen_all
in
fun rfunction pp reducer name QR (Qeqns as (QUOTE s :: _)) =
  let val nm = grab_first_ident s
      val dnm = "$"^nm
      val _ = Parse.hide nm
      val _ = Parse.hide dnm
      val eqs0 = Parse.Term Qeqns
      val lhs1 = #lhs(dest_eq(hd(strip_conj eqs0)))
      val (forig,args) = strip_comb lhs1
      val argtys = map type_of args
      val unc_argty = prod_tyl argtys
      val range_ty = type_of lhs1
      val curried = not(length args = 1)
      val unc_eqs = 
          if curried then pairf(forig,name,argtys,range_ty,eqs0) else eqs0
      val _ = Parse.reveal nm
      val _ = Parse.reveal dnm
      val R = Parse.typedTerm QR (unc_argty --> unc_argty --> Type.bool)
      fun def() = 
         let val facts = TypeBase.theTypeBase()
             val {rules,full_pats_TCs, TCs,...} = timer"making definition.\n"
                   (fn () => Tfl.gen_wfrec_definition 
                                 facts name {R=R, eqs=unc_eqs})
                    "Finished making definition.\n"
             val f = tflUtils.func_of_cond_eqn(concl(CONJUNCT1 rules handle _ => rules))
             val {induction,rules,nested_tcs} = 
                  pp{rules = rules, TCs=TCs,
                 induction = timer "starting induction proof\n"
                       (fn () => Tfl.mk_induction facts 
                            {fconst=f, R=R, SV=[], pat_TCs_list=full_pats_TCs})
                        "finished induction proof\n"} 
             val normal_tcs = termination_goals rules
             val res = case nested_tcs 
                 of [] => {induction=induction, rules=rules, tcs=normal_tcs}
                  | _  => let val (solved,simplified,stubborn) =
                          itlist (fn th => fn (So,Si,St) =>
                                  if (id_thm th) then (So, Si, th::St) else
                                  if (solved th) then (th::So, Si, St) 
                                  else (So, th::Si, St)) nested_tcs ([],[],[])
                         val simplified' = map join_assums simplified
                   in
                   {induction = reducer (solved@simplified') induction,
                        rules = reducer (solved@simplified') rules,
                          tcs = normal_tcs @
                                map (gen_all o rhs o #2 o strip_forall o concl)
                                    (simplified@stubborn)}
                   end
         in
         if curried 
         then let 
           val newvars' = variants [forig] 
                               (map (fn ty => mk_var{Name="x", Ty=ty}) argtys)
           val def = new_definition
                         (name^"_eq"^ #Name(dest_const f),
                          mk_eq{lhs=list_mk_comb (forig, newvars'), 
                                rhs=list_mk_comb(f, [list_mk_pair newvars'])})
           val rules' = Rewrite.PURE_REWRITE_RULE[GSYM def] (#rules res)
           val tcs' = map (rhs o concl o 
                           Rewrite.PURE_REWRITE_CONV[GSYM def]) (#tcs res)
           val P = #Bvar(dest_forall(concl induction))
           val Qty = itlist (fn x=>fn y=>mk_type{Tyop="fun",Args=[x,y]})
                             argtys Type.bool
           val Q = mk_var{Name = "P", Ty = Qty}
           val tm = mk_pabs{varstruct=list_mk_pair newvars',
                            body=list_mk_comb(Q,newvars')}
           val ind1 = SPEC tm 
                       (Rewrite.PURE_REWRITE_RULE[GSYM def] (#induction res))
           val ind2 = CONV_RULE (DEPTH_CONV GEN_BETA_CONV) ind1
           val induction' = GEN Q ind2
         in
               {induction=induction', rules=rules', tcs=tcs'}
         end
         else res
         end
  in def()
  end 

 end;

 (*---------------------------------------------------------------------------
  * Trivial wellfoundedness prover for combinations of wellfounded relations.
  *--------------------------------------------------------------------------*)
 fun BC_TAC th = 
   if (is_imp (#2 (Dsyntax.strip_forall (concl th))))
   then MATCH_ACCEPT_TAC th ORELSE MATCH_MP_TAC th
   else MATCH_ACCEPT_TAC th;

local open relationTheory prim_recTheory pairTheory listTheory
in
val WFthms =  [WF_inv_image, WF_measure, WF_LESS, WF_PRED, WF_LIST_PRED,
               WF_RPROD, WF_LEX, WF_TC, WF_Empty]
end;

fun WF_TAC thms = REPEAT (MAP_FIRST BC_TAC (thms@WFthms) ORELSE CONJ_TAC)


 (*---------------------------------------------------------------------------
  * Simplifier for termination conditions. 
  *--------------------------------------------------------------------------*)

local open relationTheory prim_recTheory pairTheory combinTheory
in
 val WFsimpl_thms = [measure_def, inv_image_def, RPROD_DEF, LEX_DEF]
 val simpls = WFsimpl_thms@[o_DEF,I_THM]@pairTheory.pair_rws
end;

fun tc_simplifier thl = Rules.simpl_conv (thl@simpls);


 (*--------------------------------------------------------------------------
  * A prover for termination conditions. This gets called after the
  * simplifier has simplified the conditions. 
  *--------------------------------------------------------------------------*)
val terminator = numLib.ARITH_TAC;


(* Combination of these tools. *)
fun std_postprocessor p = 
  let val fbase = TypeBase.theTypeBase()
      val datatype_simpls = rev_itlist
              (fn db => fn A => TypeBase.simpls_of db@A) 
              (TypeBase.listItems fbase) [] 
  in
  Tfl.postprocess{WFtac = WF_TAC[],
             terminator = terminator, 
             simplifier = tc_simplifier datatype_simpls} fbase p
  end;



 (*---------------------------------------------------------------------------
  * Takes a termination relation and a conjunction of recursion equations, 
  * and makes the definition, extracts termination conditions, attempts to 
  * solve them, and then derives recursion induction. Any remaining termination
  * conditions are also made available.
  *--------------------------------------------------------------------------*)
 val Rfunction = 
    let open RW
    in rfunction std_postprocessor
       (fn thl => 
          REWRITE_RULE Fully (Simpls(std_simpls, thl),
                              Context([],DONT_ADD), 
                              Congs (boolTheory.IMP_CONG::current_congs()), 
                              Solver std_solver))
    end;


 (*---------------------------------------------------------------------------
  * Takes a conjunction of recursion equations. Nested recursions are not
  * accepted. The definition of the function is then made, and termination 
  * conditions are extracted. Its name comes from the fact that a 
  * termination relation doesn't need to be given; however, one will later 
  * have to be given in order to eliminate the termination conditions.
  *--------------------------------------------------------------------------*)

fun lazyR_def name (qtm as QUOTE s::_) = 
 let val nm = grab_first_ident s
     val dnm = "$"^nm
     val _ = Parse_support.hide nm
     val _ = Parse_support.hide dnm
     val eqs0 = Parse.Term qtm
     val lhs1 = #lhs(dest_eq(hd(strip_conj eqs0)))
     val (forig,args) = strip_comb lhs1
     val given_name = #Name(dest_var forig)
     val argtys = map type_of args
     val unc_argty = prod_tyl argtys
     val range_ty = type_of lhs1
     val curried = not(length args = 1)
     val unc_eqs = 
        if curried then pairf(forig,name,argtys,range_ty,eqs0) else eqs0
     val _ = Parse_support.reveal nm
     val _ = Parse_support.reveal dnm
     fun def() = 
       let val facts = TypeBase.theTypeBase()
           val rules = #rules(Tfl.lazyR_def facts name 
                                 (Tfl.wfrec_eqns facts unc_eqs))
           val f = tflUtils.func_of_cond_eqn(concl(CONJUNCT1 rules 
                   handle HOL_ERR _ => rules))
       in        
       if curried 
       then let val newvars' = variants [forig] 
                               (map (fn ty => mk_var{Name="x", Ty=ty}) argtys)
                val def = new_definition
                         (name^"_eq_"^ #Name(dest_const f),
                          mk_eq{lhs=list_mk_comb (forig, newvars'), 
                                rhs=list_mk_comb(f, [list_mk_pair newvars'])})
            in Rewrite.PURE_REWRITE_RULE[GSYM def] rules end
       else rules
       end
 in
    def()
 end 
 

 (*---------------------------------------------------------------------------
  * Takes a conjunction of recursion equations, and makes the definition,
  * extracts termination conditions, and then derives recursion induction.
  * Termination conditions are all put on the assumptions.
  *--------------------------------------------------------------------------*)
fun function name (qtm as QUOTE s::_) = 
 let val nm = grab_first_ident s
     val dnm = "$"^nm
     val _ = Parse_support.hide nm
     val _ = Parse_support.hide dnm
     val eqs0 = Parse.Term qtm
     val lhs1 = #lhs(dest_eq(hd(strip_conj eqs0)))
     val (forig,args) = strip_comb lhs1
     val argtys = map type_of args
     val unc_argty = prod_tyl argtys
     val range_ty = type_of lhs1
     val curried = not(length args = 1)
     val unc_eqs = 
       if curried then pairf(forig,name,argtys,range_ty,eqs0) else eqs0
     val _ = Parse_support.reveal nm
     val _ = Parse_support.reveal dnm
     fun def() =
      let val facts = TypeBase.theTypeBase()
          val {rules,R,SV,full_pats_TCs,...} = timer"Making definition.\n"
                    (fn () => Tfl.lazyR_def facts name 
                                     (Tfl.wfrec_eqns facts unc_eqs))
                 "Finished definition.\n"
          val f = tflUtils.func_of_cond_eqn (concl(CONJUNCT1 rules 
                  handle HOL_ERR _ => rules))
          val induction = timer "Starting induction proof.\n"
              (fn () => Tfl.mk_induction facts 
                         {fconst=f, R=R, SV=SV, pat_TCs_list=full_pats_TCs})
              "Finished induction proof.\n"
      in 
      if curried 
      then let val newvars' = variants [forig] 
                               (map (fn ty => mk_var{Name="x", Ty=ty}) argtys)
               val def = new_definition
                         (name^"_eq_"^ #Name(dest_const f),
                          mk_eq{lhs=list_mk_comb (forig, newvars'), 
                                rhs=list_mk_comb(f, [list_mk_pair newvars'])})
               val rules' = Rewrite.PURE_REWRITE_RULE[GSYM def] rules 
               val P = #Bvar(dest_forall(concl induction))
               val Qty = itlist (fn x=>fn y=>mk_type{Tyop="fun",Args=[x,y]})
                                 argtys Type.bool
               val Q = mk_var{Name = "P", Ty = Qty}
               val tm = mk_pabs{varstruct=list_mk_pair newvars',
                                body=list_mk_comb(Q,newvars')}
               val ind1 = SPEC tm 
                      (Rewrite.PURE_REWRITE_RULE[GSYM def] induction)
               val ind2 = CONV_RULE (DEPTH_CONV GEN_BETA_CONV) ind1
           in CONJ rules' (GEN Q ind2)
           end
      else CONJ rules induction
      end
 in def()
 end

fun is_prod_ty ty = ("prod" = #Tyop(dest_type ty));
  
fun mk_vstrl [] V A = rev A
  | mk_vstrl (ty::rst) V A = 
      let val (vstr,V1) = tflUtils.mk_vstruct ty V
      in mk_vstrl rst V1 (vstr::A)
      end;

(*---------------------------------------------------------------------------
 * A simple recursion induction tactic. 
 *---------------------------------------------------------------------------*)

fun REC_INDUCT_TAC thm =
  let val {Bvar=prop,Body} = dest_forall(concl thm)
      val parg_tyl = #1(tflUtils.strip_type (type_of prop))
      val n = (length o #1 o strip_forall o #2 o strip_imp) Body
      fun ndest_forall trm = 
          let fun dest (0,tm,V) = (rev V,tm)
                | dest (n,tm,V) = let val {Bvar,Body} = dest_forall tm
                                  in dest(n-1,Body, Bvar::V) end
          in dest(n,trm,[])
          end
      fun tac (asl,w) =
       let val (V,body) = ndest_forall w
           val P = pairTools.list_mk_aabs(mk_vstrl parg_tyl V [], body)
           val thm' = CONV_RULE(DEPTH_CONV GEN_BETA_CONV) (ISPEC P thm)
       in MATCH_MP_TAC thm' (asl,w)
       end
  in tac
  end;


 (*---------------------------------------------------------------------------
  * This should actually be a "safe" STRIP_TAC, where negations are not
  * treated as implications.
  *--------------------------------------------------------------------------*)
 val SAFE_DISCH_TAC = 
     Lib.W(fn (asl,w) => if (is_neg w) then NO_TAC else DISCH_TAC);

(*---------------------------------------------------------------------------
 * A naive but useful program tactic.
 *---------------------------------------------------------------------------*)
 fun PROGRAM_TAC{induction, rules} = 
    REC_INDUCT_TAC induction 
     THEN REPEAT CONJ_TAC 
     THEN REPEAT GEN_TAC 
     THEN REPEAT SAFE_DISCH_TAC 
     THEN ONCE_REWRITE_TAC[rules]
     THEN REPEAT COND_CASES_TAC;

local 
(*---------------------------------------------------------------------------
 * "DTHEN" differs from standard DISCH_THEN in that it doesn't treat negation 
 * as implication into falsity.
 *---------------------------------------------------------------------------*)
     exception FOO;
     fun DTHEN (ttac:Abbrev.thm_tactic) :tactic = fn (asl,w) =>
       if (is_neg w) then raise FOO
       else let val {ant,conseq} = Dsyntax.dest_imp w 
                val (gl,prf) = ttac (Thm.ASSUME ant) (asl,conseq) 
            in (gl, Thm.DISCH ant o prf)
            end
     val STRIP_TAC = Tactical.FIRST[GEN_TAC,CONJ_TAC,DTHEN STRIP_ASSUME_TAC]
     open RW
     fun ROTAC thl= REWRITE_TAC Once (Pure thl,Context([],DONT_ADD), 
                                      Congs[],Solver always_fails)
     val RWTAC = REWRITE_TAC Fully (Simpls(std_simpls,[]),
                                    Context([],DONT_ADD),
                                    Congs[],Solver always_fails)
in
fun PROG_TAC{induction, rules} = 
   REC_INDUCT_TAC induction 
    THEN REPEAT CONJ_TAC 
    THEN REPEAT GEN_TAC 
    THEN ROTAC[rules]
    THEN REPEAT COND_CASES_TAC 
    THEN RWTAC
    THEN REPEAT STRIP_TAC
end;

 fun list_to_goal L = ([],list_mk_conj L);

 (*---------------------------------------------------------------------------
  * Takes the termination conditions from, e.g., the output of Rfunction 
  * and puts them into a goal stack.
  *--------------------------------------------------------------------------*)
 fun tgoal{tcs,induction,rules} = 
        (goalstackLib.set_goal o list_to_goal) tcs


 (*---------------------------------------------------------------------------
  * Applies a tactic to the termination conditions arising, e.g., from an
  * invocation of Rfunction.
  *--------------------------------------------------------------------------*)
 fun prove_termination{tcs,induction,rules} tac =
     TAC_PROOF(list_to_goal tcs,tac);


 (* Common wellfounded relations. *)
 val pred = Parse.Term`\m n. n = SUC m`;
 val list_pred = Parse.Term`\L1 L2. ?h:'a. L2 = CONS h L1`;


end;
