structure Rules :> Rules = 
struct

open Exception Lib Thm boolTheory Drule Conv Let_conv
open USyntax;
infix 3 |->

 type term = Term.term
 type hol_type = Type.hol_type
 type thm = Thm.thm
 type tactic = Abbrev.tactic

fun ERR func mesg = 
      HOL_ERR{origin_structure = "Rules",
              origin_function=func,message=mesg};


(* Inference rules *)
val REFL      = Thm.REFL
val ASSUME    = Thm.ASSUME
val MP        = Thm.MP
val MATCH_MP  = Conv.MATCH_MP
val CONJUNCT1 = Thm.CONJUNCT1
val CONJUNCT2 = Thm.CONJUNCT2
val CONJUNCTS = Drule.CONJUNCTS
val DISCH     = Thm.DISCH
val UNDISCH   = Drule.UNDISCH
val INST_TYPE = Thm.INST_TYPE o map (fn (A |-> B) => {redex=A, residue=B})
val SPEC      = Thm.SPEC
val ISPEC     = Drule.ISPEC
val ISPECL    = Drule.ISPECL
val GEN       = Thm.GEN
val GENL      = Drule.GENL
val LIST_CONJ = Drule.LIST_CONJ
val BETA_RULE = Conv.BETA_RULE;


val DISCH_ALL = Drule.DISCH_ALL
val IMP_TRANS = Drule.IMP_TRANS
val SPEC_ALL  = Drule.SPEC_ALL
val GEN_ALL   = Drule.GEN_ALL
val CHOOSE    = Thm.CHOOSE
val EXISTS    = Thm.EXISTS
val SUBS      = Drule.SUBS
val SYM       = Thm.SYM
val PROVE_HYP = Drule.PROVE_HYP
val DISJ_CASESL = Drule.DISJ_CASESL


(*---------------------------------------------------------------------------
         Capturing termination conditions.
 ----------------------------------------------------------------------------*)


local fun !!v M = Dsyntax.mk_forall{Bvar=v, Body=M}
      val mem = Lib.op_mem aconv
      fun set_diff a b = Lib.filter (fn x => not (mem x b)) a
in
fun solver (restrf,f,G,nref) simps context tm =
  let val globals = f::G  (* not to be generalized *)
      fun genl tm = itlist !! (set_diff (rev(free_vars tm)) globals) tm
      val rcontext = rev context
      val antl = case rcontext of [] => [] 
                               | _   => [list_mk_conj(map concl rcontext)]
      val TC = genl(list_mk_imp(antl, tm))
      val (R,arg,pat) = USyntax.dest_relation tm
  in 
     if can(find_term (aconv restrf)) arg
     then (nref := true; raise ERR "solver" "nested function") 
     else let val _ = if can(find_term (aconv f)) TC then nref := true else ()
          in case rcontext
              of [] => SPEC_ALL(ASSUME TC)
               | _  => MP (SPEC_ALL (ASSUME TC)) (LIST_CONJ rcontext)
          end
  end
end;

(*
local fun !!v M = Dsyntax.mk_forall{Bvar=v, Body=M}
      val mem = Lib.op_mem aconv
      fun set_diff a b = Lib.filter (fn x => not (mem x b)) a
in
fun solver (restrf,f,G,nref) simps context tm =
  let val globals = f::G  (* not to be generalized *)
      fun genl tm = itlist !! (set_diff (rev(free_vars tm)) globals) tm
      val rcontext = rev context
      val antl = case rcontext of [] => [] 
                               | _   => [list_mk_conj(map concl rcontext)]
      val (R,arg,pat) = USyntax.dest_relation tm
      val TC = genl(list_mk_imp(antl, tm))
      val _ = if can(find_term (aconv f)) TC then nref := true else ()
  in 
     if can(find_term (aconv f)) arg then raise ERR "solver" "nested function"
     else case rcontext
           of [] => SPEC_ALL(ASSUME TC)
            | _  => MP (SPEC_ALL (ASSUME TC)) (LIST_CONJ rcontext)
  end
end;
*)

fun sthat P x = P x handle Interrupt => raise Interrupt
                         |     _     => false;


(*
local fun is_restr tm = (#Name(dest_const tm) = "RESTRICT")
      val restricted = can(find_term(sthat is_restr))
in
*)

fun CONTEXT_REWRITE_RULE (restrf,f,G,nr) {thms,congs,th} = 
  let open RW 
  in
     REWRITE_RULE Fully 
         (Pure thms, Context([],DONT_ADD), Congs congs,
          Solver(solver (restrf,f,G,nr))) th
  end;


fun simpl_conv thl = 
  let open RW
      val RWC = Rewrite Fully 
                   (Simpls(std_simpls,thl), 
                    Context([],DONT_ADD),Congs[],Solver always_fails)
      fun simpl tm =
       let val th = Conv.THENC(RWC, Conv.DEPTH_CONV GEN_BETA_CONV) tm
           val {lhs,rhs} = dest_eq(concl th)
       in if (aconv lhs rhs) then th else TRANS th (simpl rhs)
       end
  in simpl
  end;


fun simplify thl = 
  let val rewrite = RW.PURE_RW_RULE thl
      fun simpl th =
       let val th' = CONV_RULE (DEPTH_CONV GEN_BETA_CONV) (rewrite th)
           val (_,c1) = dest_thm th
           val (_,c2) = dest_thm th'
       in if (aconv c1 c2) then th else simpl th'
       end
  in simpl
  end;

val RIGHT_ASSOC = RW.PURE_RW_RULE[GSYM DISJ_ASSOC];


fun FILTER_DISCH_ALL P th =
   let val (asl,_) = dest_thm th
   in itlist DISCH (filter (sthat P) asl) th
   end;

(*----------------------------------------------------------------------------
 *
 *         A |- M
 *   -------------------   [v_1,...,v_n]
 *    A |- ?v1...v_n. M
 *
 *---------------------------------------------------------------------------*)
fun EXISTL vlist thm =
   itlist (fn v => fn thm => EXISTS(mk_exists{Bvar=v,Body=concl thm},v) thm)
          vlist thm;

(*----------------------------------------------------------------------------
 *
 *       A |- M[x_1,...,x_n]
 *   ----------------------------   [(x |-> y)_1,...,(x |-> y)_n]
 *       A |- ?y_1...y_n. M
 *
 *---------------------------------------------------------------------------*)
fun IT_EXISTS theta thm =
 itlist (fn (b as (redex |-> residue)) => fn thm => 
    EXISTS(mk_exists{Bvar=residue, Body=subst [b] (concl thm)},
            redex) thm)
    theta thm;



(*----------------------------------------------------------------------------
 *
 *                   A1 |- M1, ..., An |- Mn
 *     ---------------------------------------------------
 *     [A1 |- M1 \/ ... \/ Mn, ..., An |- M1 \/ ... \/ Mn]
 *
 *---------------------------------------------------------------------------*)

fun EVEN_ORS thms =
  let fun blue ldisjs [] _ = []
        | blue ldisjs (th::rst) rdisjs =
            let val rdisj_tl = list_mk_disj(Lib.trye tl rdisjs)
            in itlist DISJ2 ldisjs (DISJ1 th rdisj_tl)
               :: blue (ldisjs@[concl th]) rst (Lib.trye tl rdisjs)
            end 
            handle HOL_ERR _ => [itlist DISJ2 ldisjs th]
   in
   blue [] thms (map concl thms)
   end;


val prove = Tactical.prove;

end; (* Rules *)
