(****************************************************************************)
(* FILE          : equalities.sml                                           *)
(* DESCRIPTION   : Using equalities.                                        *)
(*                                                                          *)
(* AUTHOR (HOL88): R.J.Boulton                                              *)
(* DATE          : 19th June 1991                                           *)
(*                                                                          *)
(* TRANSLATED BY : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(*                                                                          *)
(* LAST MODIFIED : R.J.Boulton                                              *)
(* DATE          : 4th October 1995                                         *)
(****************************************************************************)

structure BoyerMooreEqualities =
struct

local

open HolKernel Parse basicHol90Lib Psyntax BoyerMooreSupport;
infix ## THEN;

fun failwith function =
   raise HOL_ERR {origin_structure = "BoyerMooreEqualities",
                  origin_function = function,
                  message = ""};

in

(*--------------------------------------------------------------------------*)
(* is_explicit_value_template : term -> bool                                *)
(*                                                                          *)
(* Function to compute whether a term is an explicit value template.        *)
(* An explicit value template is a non-variable term composed entirely of   *)
(* T or F or variables or applications of shell constructors.               *)
(* A `bottom object' corresponds to an application to no arguments. I have  *)
(* also made numeric constants valid components of explicit value           *)
(* templates, since they are equivalent to some number of applications of   *)
(* SUC to 0.                                                                *)
(*--------------------------------------------------------------------------*)

fun is_explicit_value_template tm =
   let fun is_explicit_value_template' constructors tm =
          (is_T tm) orelse (is_F tm) orelse
          ((is_const tm) andalso (type_of tm = (==`:num`==))) orelse
          (is_var tm) orelse
          let val (f,args) = strip_comb tm
          in  (mem (#Name (Rsyntax.dest_const f)) constructors
               handle HOL_ERR _ => false) andalso
              (forall (is_explicit_value_template' constructors) args)
          end
   in  (not (is_var tm)) andalso
       (is_explicit_value_template' (BoyerMooreShells.all_constructors ()) tm)
   end;

(*--------------------------------------------------------------------------*)
(* subst_conv : thm -> conv                                                 *)
(*                                                                          *)
(* Substitution conversion. Given a theorem |- l = r, it replaces all       *)
(* occurrences of l in the term with r.                                     *)
(*--------------------------------------------------------------------------*)

fun subst_conv th tm = SUBST_CONV [(th,lhs (concl th))] tm tm;

(*--------------------------------------------------------------------------*)
(* use_equality_subst : bool -> bool -> thm -> conv                         *)
(*                                                                          *)
(* Function to perform substitution when using equalities. The first        *)
(* argument is a Boolean that controls which side of an equation            *)
(* substitution is to take place on. The second argument is also a Boolean, *)
(* indicating whether or not we have decided to cross-fertilize. The third  *)
(* argument is a substitution theorem of the form:                          *)
(*                                                                          *)
(*    t' = s' |- t' = s'                                                    *)
(*                                                                          *)
(* If we are not cross-fertilizing, s' is substituted for t' throughout the *)
(* term. If we are cross-fertilizing, the behaviour depends on the          *)
(* structure of the term, tm:                                               *)
(*                                                                          *)
(*    (a) if tm is (--`l = r`--), substitute s' for t' in either r or l.    *)
(*    (b) if tm is (--`~(l = r)`--), substitute s' for t' throughout tm.    *)
(*    (c) otherwise, do not substitute.                                     *)
(*--------------------------------------------------------------------------*)

(* The heuristic above is modified so that in case (c) a substitution does  *)
(* take place. This reduces the chances of an invalid subgoal (clause)      *)
(* being generated, and has been shown to be a better option for certain    *)
(* examples.                                                                *)

fun use_equality_subst right cross_fert th tm =
   (if cross_fert
    then if (is_eq tm)
         then if right
              then RAND_CONV (subst_conv th) tm
              else RATOR_CONV (RAND_CONV (subst_conv th)) tm
         else if ((is_neg tm) andalso
                  (is_eq (rand tm) handle HOL_ERR _ => false))
              then subst_conv th tm
              else (* ALL_CONV tm *) subst_conv th tm
    else subst_conv th tm)
   handle HOL_ERR _ => failwith "use_equality_subst";

(*--------------------------------------------------------------------------*)
(* EQ_EQ_IMP_DISJ_EQ =                                                      *)
(* |- !x x' y y'. (x = x') /\ (y = y') ==> (x \/ y = x' \/ y')              *)
(*--------------------------------------------------------------------------*)

val EQ_EQ_IMP_DISJ_EQ =
   prove
      ((--`!x x' y y'. (x = x') /\ (y = y') ==> ((x \/ y) = (x' \/ y'))`--),
       REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC []);

(*--------------------------------------------------------------------------*)
(* DISJ_EQ : thm -> thm -> thm                                              *)
(*                                                                          *)
(*     |- x = x'    |- y = y'                                               *)
(*    ------------------------                                              *)
(*    |- (x \/ y) = (x' \/ y')                                              *)
(*--------------------------------------------------------------------------*)

fun DISJ_EQ th1 th2 =
   let val (x,x') = dest_eq (concl th1)
       and (y,y') = dest_eq (concl th2)
   in  MP (SPECL [x,x',y,y'] EQ_EQ_IMP_DISJ_EQ) (CONJ th1 th2)
   end
   handle HOL_ERR _ => failwith "DISJ_EQ";

(*--------------------------------------------------------------------------*)
(* use_equality_heuristic : (term * bool) -> ((term * bool) list * proof)   *)
(*                                                                          *)
(* Heuristic for using equalities, and in particular for cross-fertilizing. *)
(* Given a clause, the function looks for a literal of the form ~(s' = t')  *)
(* where t' occurs in another literal and is not an explicit value          *)
(* template. If no such literal is present, the function looks for a        *)
(* literal of the form ~(t' = s') where t' occurs in another literal and is *)
(* not an explicit value template. If a substitution literal of one of      *)
(* these two forms is found, substitution takes place as follows.           *)
(*                                                                          *)
(* If the clause is an induction step, and there is an equality literal     *)
(* mentioning t' on the RHS (or LHS if the substitution literal was         *)
(* ~(t' = s')), and s' is not an explicit value, the function performs a    *)
(* cross-fertilization. The substitution function is called for each        *)
(* literal other than the substitution literal. Each call results in a      *)
(* theorem of the form:                                                     *)
(*                                                                          *)
(*    t' = s' |- old_lit = new_lit                                          *)
(*                                                                          *)
(* If the clause is an induction step and s' is not an explicit value, the  *)
(* substitution literal is rewritten to F, and so will subsequently be      *)
(* eliminated. Otherwise this literal is unchanged. The theorems for each   *)
(* literal are recombined using the DISJ_EQ rule, and the new clause is     *)
(* returned. See the comments for the substitution heuristic for a          *)
(* description of how the original clause is proved from the new clause.    *)
(*--------------------------------------------------------------------------*)

fun use_equality_heuristic (tm,(ind:bool)) =
   let fun check (tml1,tml2) t' =
          (not (is_explicit_value_template t')) andalso
          ((exists (BoyerMooreDefinitions.is_subterm t') tml1) orelse
           (exists (BoyerMooreDefinitions.is_subterm t') tml2))
       fun split_disjuncts side prevl [] = failwith "split_disjuncts"
         | split_disjuncts side prevl (tml as tm::tms) =
          if (can (assert (check (prevl,tms)) o side o dest_neg) tm)
          then (prevl,tml)
          else split_disjuncts side (tm::prevl) tms
       fun is_subterm_of_side side subterm tm =
          BoyerMooreDefinitions.is_subterm subterm (side tm)
          handle HOL_ERR _ => false
       val literals = disj_list tm
       val (right,(overs,neq'unders)) =
          (true,(rev ## I) (split_disjuncts rhs [] literals))
          handle HOL_ERR _ =>
          (false,(rev ## I) (split_disjuncts lhs [] literals))
       val (neq',unders) =
          case neq'unders of x::xs => (x,xs) | [] => failwith ""
       val side = if right then rhs else lhs
       val flipth = if right then ALL_CONV neq' else RAND_CONV SYM_CONV neq'
       val neq = rhs (concl flipth)
       val eq = dest_neg neq
       val (s',t') = dest_eq eq
       val delete =
          ind andalso not (BoyerMooreDefinitions.is_explicit_value s')
       val cross_fert = delete andalso
                        ((exists (is_subterm_of_side side t') overs) orelse
                         (exists (is_subterm_of_side side t') unders))
       val sym_eq = mk_eq (t',s')
       val sym_neq = mk_neg sym_eq
       val ass1 = EQ_MP (SYM flipth) (NOT_EQ_SYM (ASSUME sym_neq))
       and ass2 = ASSUME sym_eq
       val subsfun = use_equality_subst right cross_fert ass2
       val overths = map subsfun overs
       and neqth =
          if delete
          then TRANS (RAND_CONV (RAND_CONV (subst_conv ass2)) neq)
                  (ISPEC s' BoyerMooreTermsAndClauses.NOT_EQ_F)
          else ADD_ASSUM sym_eq (REFL neq)
       and underths = map subsfun unders
       val neqth' = TRANS flipth neqth
       val th1 = itlist DISJ2 overs
                    (DISJ1 ass1 (list_mk_disj unders) handle HOL_ERR _ => ass1)
       and th2 = itlist DISJ_EQ overths (end_itlist DISJ_EQ (neqth'::underths))
       and th3 = SPEC sym_eq EXCLUDED_MIDDLE
       val tm' = rhs (concl th2)
       fun proof th = DISJ_CASES th3 (EQ_MP (SYM th2) th) th1
   in  ([(tm',ind)],BoyerMooreWaterfall.apply_proof (proof o hd) [tm'])
   end
   handle HOL_ERR _ => failwith "use_equality_heuristic";

end;

end; (* BoyerMooreEqualities *)
