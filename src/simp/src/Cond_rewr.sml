structure Cond_rewr :> Cond_rewr = struct

open HolKernel Parse Drule Conv boolTheory
     Psyntax liteLib Trace Ho_match Ho_rewrite;

val (Type,Term) = parse_from_grammars boolTheory.bool_grammars
fun -- q x = Term q
fun == q x = Type q



type term = Term.term
type thm  = Thm.thm
type conv = Abbrev.conv;

infix |-> ##

fun WRAP_ERR x = STRUCT_WRAP "Cond_rewr" x;
fun ERR x = STRUCT_ERR "Cond_rewr" x;

val stack_limit = ref 4;

(* -----------------------------------------------------------------------*
 * A total ordering on terms.  The behaviour of the simplifier depends    *
 * on this, so don't change it without thinking.                          *
 *                                                                        *
 * Based on some code in Isabelle.                                        *
 *                                                                        *
 * a strict (not reflexive) linear well-founded AC-compatible ordering    *
 * for terms.                                                             *
 *                                                                        *
 * Modified by DRS to have certain AC properties.  Vars are always        *
 * bigger than constants (hence move to the right).  They are             *
 * also bigger than unary comb functions.  They can't be bigger than      *
 * 2 or more argument functions as AC rewriting then loops (you           *
 * need var < f(var2,var3))                                               *
 * -----------------------------------------------------------------------*)

fun size_of_term tm =
       case (dest_term tm) of
          LAMB{Bvar,Body} => 1 + size_of_term Body
        | COMB{Rator,Rand} => size_of_term Rator + size_of_term Rand
        | _ => 1


   fun ac_term_ord(tm1,tm2) =
   (case (dest_term tm1, dest_term tm2) of
      (VAR _,CONST _) => GREATER
    | (VAR _, COMB {Rator,Rand}) => if is_comb Rator then LESS else GREATER
    | (CONST _, VAR _) => LESS
    | (COMB {Rator,Rand}, VAR _) => if is_comb Rator then GREATER else LESS
    | (VAR v1, VAR v2) => String.compare(#Name v1,#Name v2)
    | (CONST c1, CONST c2) => String.compare(#Name c1,#Name c2)
    | (dt1,dt2) =>
      (case Int.compare (size_of_term tm1,size_of_term tm2) of
       EQUAL =>
         (case (dt1,dt2) of
            (LAMB l1,LAMB l2) => ac_term_ord(#Body l1,#Body l2)
          | _ => let val (con,args) = strip_comb tm1
                     val (con2,args2) = strip_comb tm2
                 in case ac_term_ord (con,con2) of
                    EQUAL => list_ord ac_term_ord (args,args2)
                  | ord => ord
                 end)
       | ord => ord))

   (* ---------------------------------------------------------------------
    * COND_REWR_CONV
    * ---------------------------------------------------------------------*)

   fun vperm(tm1,tm2) =
      case (dest_term tm1, dest_term tm2) of
         (VAR v1,VAR v2)   => (#Ty v1= #Ty v2)
       | (LAMB t1,LAMB t2) => vperm(#Body t1,#Body t2)
       | (COMB t1,COMB t2) => vperm(#Rator t1,#Rator t2)
                      andalso vperm(#Rand t1, #Rand t2)
       | (x,y) => (x = y)

   fun is_var_perm(tm1,tm2) =
       vperm(tm1,tm2) andalso set_eq (free_vars tm1) (free_vars tm2)

   fun COND_REWR_CONV th =
      let val eqn = snd (strip_imp (concl th))
          val isperm = is_var_perm (dest_eq eqn)
          val instth = PART_MATCH (lhs o snd o strip_imp) th
                       handle HOL_ERR _ => ERR("COND_REWR_CONV",
                         "bad theorem argument (not an conditional equation)")
      in
      fn solver => fn stack => fn tm =>
       (let val conditional_eqn = instth tm
            val (conditions,eqn) = strip_imp (concl conditional_eqn)
	    val _ = if exists (C (op_mem aconv) stack) conditions
			then (trace(1, TEXT "looping - cut");
                              failwith "looping!") else ()
	    val _ = if length stack + length conditions > (!stack_limit)
                    then (trace(1, TEXT "looping - stack limit reached");
                          failwith "stack limit") else ()
            val (l,r) = dest_eq eqn
            val _ =
              if Term.aconv l r then
                (trace(1, IGNORE ("Rewrite loops", conditional_eqn));
                 failwith "looping rewrite")
              else ()

            val _ = if (isperm andalso (ac_term_ord(r,l) <> LESS))
                    then failwith "permutative rewr: not applied" else ()
            val _ = if null conditions then ()
                    else trace(if isperm then 2 else 1, REWRITING(tm,th))
	    val new_stack = conditions@stack
            fun solver' condition =
                 let val _   = trace(2,SIDECOND_ATTEMPT condition)
                     val res = solver new_stack condition
                      handle e as HOL_ERR _
                       =>  (trace(1,SIDECOND_NOT_SOLVED condition); raise e)
                 in trace(2,SIDECOND_SOLVED res);
                    res
                 end
            val condition_thms = map solver' conditions
            val disch_eqn = rev_itlist (C MP) condition_thms conditional_eqn
            val final_thm = if (l = tm) then disch_eqn
                            else TRANS (ALPHA tm l) disch_eqn
            val _ = if null conditions then
              trace(if isperm then 2 else 1, REWRITING(tm,th))
                    else ()
        in trace(if isperm then 3 else 2,PRODUCE(tm,"rewrite",final_thm));
	    final_thm
        end
        handle e as (HOL_ERR _) => WRAP_ERR("COND_REWR_CONV (application)",e))
      end
      handle e as (HOL_ERR _) => WRAP_ERR("COND_REWR_CONV (construction) ",e);


fun loops th =
   let val (l,r) = dest_eq (concl th)
   in (can (find_term (fn tm => l = tm)) r)
   end handle HOL_ERR _ => failwith "loops"


(*-------------------------------------------------------------------------
 * IMP_CONJ_THM
 * IMP_CONJ_RULE
 * CONJ_DISCH
 *
 * CONJ_DISCH discharges a list of assumptions, and conjoins them as
 * a single antecedent.
 *
 * EXAMPLE
 *
 * CONJ_DISCH [`P:bool`,`Q:bool`] (mk_thm([`P:bool`,`Q:bool`,`R:bool`],`T`));
 * val it = [R] |- P /\ Q ==> T : thm
 *------------------------------------------------------------------------*)


val CONJ_DISCH =
  let val IMP_CONJ_RULE =
      let val IMP_CONJ_THM = TAUT (--`(P ==> Q ==> R) ==> (P /\ Q ==> R)`--);
          val P = mk_var("P",Type.bool)
          and Q = mk_var("Q",Type.bool)
          and R = mk_var("R",Type.bool)
      in fn th =>
        let val (p,qr) = dest_imp(concl th)
            val (q,r) = dest_imp qr
        in MP (INST [P |-> p, Q |-> q, R |-> r] IMP_CONJ_THM) th
        end
      end;
  in fn asms => fn th =>
    itlist (fn tm => (fn th => IMP_CONJ_RULE th
                      handle HOL_ERR _ => th) o DISCH tm)
    asms th
  end;



  (* ----------------------------------------------------------------------
   * IMP_EQ_CANON
   *
   * Put a theorem into canonical form as a conditional equality.
   *
   * Makes the set of rewrites from a given theorem.
   * Split a theorem into a list of theorems suitable for rewriting:
   *   1. Specialize all variables (SPEC_ALL).
   *   2. Move all conditions into assumptions
   *   3. Then do the following:
   *     A |- t1 /\ t2     -->    [A |- t1 ; A |- t2]
   *   4. Then A |- t --> [A |- t = T]
   *           A |- ~(t1 = t2) -> [A |- (t1 = t2) = F; A |- (t2 = t1) = F]
   *           A |- ~t --> A |- [t = F]
   *           A |- F --> thrown away  (hmmm... a bit suss)
   *           A |- T --> thrown away
   *   5. Discharge all conditions as one single conjoined condition.
   *   6. Existentially quantify variables free in the conditions
   *      but not free in the equation.
   *
   * EXAMPLES
   *
   * IMP_EQ_CANON [mk_thm([],`foo (s1,s2) ==> P s2`];
   * IMP_EQ_CANON (mk_thm([],`foo (s1,s2) ==> (v1 = v2)`));
   * ----------------------------------------------------------------------*)
(* new version of this due to is_imp/negation problem in hol90 *)
fun UNDISCH_ALL th =
  if is_imp (concl th) then UNDISCH_ALL (UNDISCH th)
  else th;;


val truth_tm = (--`T`--);
val false_tm = (--`F`--);
fun IMP_EQ_CANON thm =
   let val conditions = #1 (strip_imp (concl thm))
       val undisch_thm = UNDISCH_ALL thm
       val conc = concl undisch_thm
       val undisch_rewrites =
        if (is_eq conc)
        then if (loops undisch_thm)
             then (trace(1,IGNORE("looping rewrite",thm)); [])
             else if null (subtract (free_vars (rhs conc))
			   (free_varsl (hyp thm)@free_vars(lhs conc)))
		      then [undisch_thm]
		  else [EQT_INTRO undisch_thm]
        else if (is_conj conc)
        then (op @ o (IMP_EQ_CANON##IMP_EQ_CANON) o CONJ_PAIR) undisch_thm
        else if (is_forall conc)
        then IMP_EQ_CANON (snd (SPEC_VAR undisch_thm))
        else if (is_neg conc)
             then if (is_eq (dest_neg conc))
                  then [EQF_INTRO undisch_thm, EQF_INTRO (GSYM undisch_thm)]
                  else [EQF_INTRO undisch_thm]
        else if conc = truth_tm
        then (trace(2,IGNORE ("pointless rewrite",thm)); [])
        else if (conc = false_tm)
        then (trace(2,IGNORE("contradictory rewrite (for safety)",thm)); [])
        else [EQT_INTRO undisch_thm]
   in
      map (CONJ_DISCH conditions) undisch_rewrites
   end
handle e as HOL_ERR _ => WRAP_ERR("IMP_EQ_CANON",e);


fun QUANTIFY_CONDITIONS thm =
  if is_imp (concl thm)
  then let val free_in_eqn = (free_vars (snd(dest_imp (concl thm))))
           val free_in_thm = (free_vars (concl thm))
           val free_in_hyp = free_varsl (hyp thm)
           val free_in_conditions =
                 subtract (subtract free_in_thm free_in_eqn) free_in_hyp
           fun quantify fv = CONV_RULE (REWR_CONV LEFT_FORALL_IMP_THM) o GEN fv
           val quan_thm = itlist quantify free_in_conditions thm
       in [quan_thm]
       end
  else [thm] handle e as HOL_ERR _ => WRAP_ERR("QUANTIFY_CONDITIONS",e);


fun IMP_CANON th =
 let val w = concl th
 in if (is_conj w)
    then IMP_CANON (CONJUNCT1 th) @ IMP_CANON (CONJUNCT2 th) else
    if (is_imp w)
    then
    let val (ant,_) = dest_imp w
    in if (is_conj ant)
       then let val (conj1,conj2) = dest_conj ant
            in IMP_CANON
                (DISCH conj1 (DISCH conj2
                    (MP th (CONJ (ASSUME conj1) (ASSUME conj2)))))
            end else
       if (is_disj ant)
       then let val (disj1,disj2) = dest_disj ant
            in IMP_CANON (DISCH disj1 (MP th (DISJ1 (ASSUME disj1) disj2)))
               @
               IMP_CANON (DISCH disj2 (MP th (DISJ2 disj1 (ASSUME disj2))))
            end else
       if (is_exists ant)
       then let val (Bvar,Body) = dest_exists ant
                val bv' = variant (thm_free_vars th) Bvar
                val body' = subst [Bvar |-> bv'] Body
            in
              IMP_CANON (DISCH body' (MP th (EXISTS(ant, bv') (ASSUME body'))))
            end
       else map (DISCH ant) (IMP_CANON (UNDISCH th))
    end
    else if (is_forall w) then IMP_CANON (SPEC_ALL th) else [th]
 end;


infix oo;
fun f oo g = fn x => flatten (map f (g x));

fun mk_cond_rewrs l =
    (QUANTIFY_CONDITIONS oo IMP_EQ_CANON oo IMP_CANON) l
    handle e as HOL_ERR _ => WRAP_ERR("mk_cond_rewrs",e);

end (* struct *)


(* TESTS:
 SIMP_CONV sum_ss [] (--`ISL y ==> (y = INL (OUTL y))`--);


val th1 = ASSUME (--`!(x:num) (y:num). Q x y ==> R x`--);

    SIMP_CONV (merge_ss [bool_ss,SATISFY_ss]) [th1] (--`Q 1 3 ==> R 1`--);



*)
