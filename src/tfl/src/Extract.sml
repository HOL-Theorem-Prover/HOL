structure Extract :> Extract =
struct

open HolKernel Parse boolLib pairLib Rules;

val ERR = mk_HOL_ERR "Extract";

val monitoring = ref 0

val _ = register_trace ("TFL TC-extraction monitoring", monitoring, 20);

fun lztrace(i,fname,msgf) =
  if i <= !monitoring then
     Lib.say ("\nExtract."^fname^": "^ msgf() ^ "\n")
  else ()

(* Fix the grammar used by this file *)
val ambient_grammars =
  Parse.current_grammars()
  before Parse.temp_set_grammars boolTheory.bool_grammars;

fun pp_terms ts =
 let open HOLPP
 in block CONSISTENT 0 (pr_list pp_term [NL] ts)
 end

exception EXTRACTION_ERROR of thm list * term

(*----------------------------------------------------------------------------
 * |- !x y z. w   --->  |- w[x|->g1][y|->g2][z|->g3]
 * This belongs in Drule.sml.
 *---------------------------------------------------------------------------*)

fun GSPEC_ALL th =
   (case (dest_thy_const(rator (concl th)))
     of {Name = "!",Thy="bool",Ty} =>
          GSPEC_ALL (SPEC (genvar (#1(dom_rng(#1(dom_rng Ty))))) th)
     | _ => th)
    handle HOL_ERR _ => th;

fun gvterm tm =
  case dest_term tm
   of COMB(t1,t2) => mk_comb(gvterm t1,gvterm t2)
    | LAMB(v,M) =>
       let val gv = genvar (type_of v)
           val M' = gvterm(subst [v |-> gv] M)
       in mk_abs(gv,M')
       end
    | otherwise => tm;

fun GENVAR_THM th =
 let val M = concl th
     val M' = gvterm M
 in
  EQ_MP (ALPHA M M') th
 end;

(* ---------------------------------------------------------------------------
 * Split a theorem into a list of theorems suitable for rewriting:
 *
 *   Apply the following transformations:
 *
 *        |t1 /\ t2|     -->    |t1| @ |t2|
 *        |t1 ==> t2|    -->    (t1 |- |t2|)
 *        |!x.tm|        -->    |{x |-> newvar}tm|
 *
 *   Bottom-out with |- t --> |- t = T and |- ~t --> |- t = F
 *
 *---------------------------------------------------------------------------*)

 fun mk_simpls SPECer =
  let fun mk_rewrs th =
      let val tm = Thm.concl th
      in  if (is_eq tm) then [th] else
          if (is_neg tm) then [EQF_INTRO th] else
          if (is_conj tm)
          then (op @ o (mk_rewrs ## mk_rewrs) o Drule.CONJ_PAIR) th else
          if (is_imp tm)
          then let val ant = list_mk_conj (fst(strip_imp_only tm))
                   fun step imp cnj =
                       step (MP imp (CONJUNCT1 cnj)) (CONJUNCT2 cnj)
                       handle HOL_ERR _ => MP imp cnj
               in EQT_INTRO th
                  ::map (DISCH ant) (mk_rewrs (step th (ASSUME ant)))
               end else
          if (is_forall tm) then mk_rewrs (SPECer th) else
          if aconv tm boolSyntax.T then [] else
          [EQT_INTRO th]
      end
      handle HOL_ERR _ => raise ERR "mk_simpls" ""
  in
    mk_rewrs
  end;

 fun mk_simplsl SPECer = flatten o map (mk_simpls SPECer);

 local val MK_FRESH = mk_simpls GSPEC_ALL        (* partly apply *)
       val MK_READABLE = mk_simpls SPEC_ALL      (* partly apply *)
 in
 fun MK_RULES_APART th = MK_FRESH (GEN_ALL th)
 and MK_RULES th = MK_READABLE (GEN_ALL th)
 end;


(* Provides a quick way of telling if a rewrite rule is conditional or not. *)
datatype choice = COND of thm | UNCOND of thm;

fun dest_choice (COND th)   = th
  | dest_choice (UNCOND th) = th;

(*----------------------------------------------------------------------------
 * Takes a rewrite rule and applies it to a term, which, if it is an instance
 * of the left-hand side of the rule, results in the return of the
 * instantiated rule. Handles conditional rules.
 *---------------------------------------------------------------------------*)

fun PRIM_RW_CONV th =
 let val (has_condition,eq) = ((not o null)##I)(strip_imp_only (concl th))
     val pat = lhs eq
     val matcher = Term.match_term pat
     fun match_then_inst tm =
        let val (tm_theta, ty_theta) = matcher tm
            val th' = INST tm_theta (INST_TYPE ty_theta th)
        in
          if has_condition then (COND th') else (UNCOND th')
        end
 in match_then_inst
 end;


(*----------------------------------------------------------------------------
 * Match and instantiate a congruence rule. A congruence rule looks like
 *
 *        (c1 ==> (M1 = M1')) /\ .../\ (cm ==> (Mn = Mn'))
 *       -------------------------------------------------
 *                    f M1...Mn = f M1'...Mn'
 *
 * The ci do not have to be there, i.e., unconditional antecedents can
 * certainly exist.
 *---------------------------------------------------------------------------*)

fun CONGR th =
   let val (ants,eq) = strip_imp_only (concl th)
       (* TODO: Check that it is a congruence rule *)
       val pat = lhs eq
       val matcher = Term.match_term pat
       fun match_then_inst tm =
          let val (tm_theta, ty_theta) = matcher tm
          in INST tm_theta (INST_TYPE ty_theta th) end
   in
     match_then_inst
   end;

datatype simpls = RW of {thms     : thm list list,
                        congs    : thm list list,
                        rw_net   : (term -> choice) Net.net,
                        cong_net : (term -> thm) Net.net};

val empty_simpls = RW{thms = [[]],  congs = [[]],
                      rw_net = Net.empty,
                      cong_net = Net.empty};

fun dest_simpls (RW{thms, congs,...}) =
   {rws = rev(flatten thms),
    congs = rev(flatten congs)};


fun add_rws (RW{thms,rw_net,congs, cong_net}) thl =
 RW{thms   = thl::thms,
    congs  = congs,
  cong_net = cong_net,
    rw_net = itlist Net.insert
             (map (fn th => let val left = lhs(#2(strip_imp_only(concl th)))
                            in  (left,  PRIM_RW_CONV th) end)
                  (flatten (map MK_RULES_APART thl)))        rw_net}
 handle HOL_ERR _
 => raise ERR "add_rws" "Unable to deal with input";


fun add_congs (RW{cong_net, congs, thms, rw_net}) thl =
  RW{thms = thms, rw_net = rw_net,
     congs = thl::congs,
     cong_net = itlist Net.insert
         (map (fn th =>
                let val c = concl th
                    val eq = snd(dest_imp c) handle HOL_ERR _ => c
                in
                   (lhs eq,  CONGR th)
                end)
              (map (GSPEC_ALL o GEN_ALL) thl))         cong_net}
  handle HOL_ERR _ =>
  raise ERR"add_congs" "Unable to deal with input"

(*----------------------------------------------------------------------------
 *                          Prettyprinting
 *---------------------------------------------------------------------------*)

local open Portable PP
in
fun pp_simpls (RW{thms,congs,...}) =
   let val pp_thm = Parse.pp_thm
       val thms' = mk_simplsl SPEC_ALL (rev(flatten thms))
       val congs' = rev(flatten congs)
       val how_many_thms = length thms'
       val how_many_congs = length congs'
       val B = block CONSISTENT 0
   in
     block PP.CONSISTENT 0 [
       if how_many_thms = 0
       then add_string "<empty simplification set>"
       else B [add_string"Rewrite Rules:", NL,
               add_string"--------------", NL,
               block PP.INCONSISTENT 0 (
                 pr_list pp_thm [add_string";", add_break(2,0)] thms')
              ],
       NL,
       add_string("Number of rewrite rules = "^Lib.int_to_string how_many_thms),
       NL,
       B (if (how_many_congs = 0) then []
          else [
            NL,
            add_string"Congruence Rules", NL,
            add_string"----------------", NL,
            B (pr_list pp_thm [add_string";", add_break(2,0)] congs'), NL,
            add_string("Number of congruence rules = "
                       ^Lib.int_to_string how_many_congs), NL
         ])
     ]
   end
end;

(*----------------------------------------------------------------------------
 * In RW_STEP, we find the list of matching rewrites, and choose the first
 * one that succeeds. Conditional rules succeed if they can solve their
 * antecedent by applying the prover (it gets to use the context and the
 * supplied simplifications).
 * Note.
 * "ant_vars_fixed" is true when the instantiated rewrite rule has no
 * uninstantiated variables in its antecedent. If "ant_vars_fixed" is not
 * true, we get the instantiation from the context.
 *
 * Note.
 * "sys_var" could be more rigorous in its check, but we don't
 * have a defined notion of the syntax of system variables.
 *---------------------------------------------------------------------------*)

local
  fun sys_var tm =
     is_var tm andalso
     not (Lexis.is_clean_varname (fst (dest_var tm)))
in
fun RW_STEP {simpls as RW{rw_net,...},context,prover} tm = let
  fun match f =
      (case f tm of
         UNCOND th => SOME th
       | COND th => let
           val condition = fst(dest_imp(concl th))
           val cond_thm = prover context condition
          val ant_vars_fixed = not(can(find_term sys_var) condition)
         in
           SOME ((if ant_vars_fixed then MP else MATCH_MP) th cond_thm)
         end)
      handle HOL_ERR _ => NONE
  fun try [] = raise ERR "RW_STEP" "all applications failed"
    | try (f::rst) =
      case match f of
        NONE => try rst
      | SOME th =>
        if !monitoring > 0 then
          (set_trace "assumptions" 1;
           Lib.say (String.concat
              ["\nTC Capture:\n", Parse.thm_to_string th, "\n\n"]);
           th before
           set_trace "assumptions" 0)
        else th
in
   try (Net.match tm rw_net)
end end

(*---------------------------------------------------------------------------
 * It should be a mistake to have more than one applicable congruence rule for
 * a constant, but I don't currently check that.
 *---------------------------------------------------------------------------*)

fun CONG_STEP (RW{cong_net,...}) tm = Lib.trye hd (Net.match tm cong_net) tm;

(*---------------------------------------------------------------------------*)
(*                             TERM TRAVERSAL                                *)
(*---------------------------------------------------------------------------*)

exception UNCHANGED;

fun QCONV cnv cp tm = cnv cp tm handle UNCHANGED => REFL tm;

val ALL_QCONV = fn _ => raise UNCHANGED;

fun THENQC cnv1 cnv2 cp tm =
   let val th1 = cnv1 cp tm
   in TRANS th1 (cnv2 cp (rhs (concl th1))) handle UNCHANGED => th1
   end
   handle UNCHANGED => cnv2 cp tm;

fun ORELSEQC cnv1 cnv2 cp tm =
   cnv1 cp tm handle UNCHANGED => raise UNCHANGED
                   | HOL_ERR _ => cnv2 cp tm;

fun REPEATQC conv cp tm =
   ORELSEQC (THENQC conv (REPEATQC conv)) ALL_QCONV cp tm;

local val CHANGED_ERR = ERR "CHANGED_QCONV" ""
in
fun CHANGED_QCONV cnv cp tm =
   let val th = cnv cp tm handle UNCHANGED => raise CHANGED_ERR
       val (lhs,rhs) = dest_eq (concl th)
   in if aconv lhs rhs then raise CHANGED_ERR else th
   end
end;

fun TRY_QCONV cnv = ORELSEQC cnv ALL_QCONV;

datatype delta
  = CHANGE of thm
  | NO_CHANGE of thm

fun unchanged (NO_CHANGE _) = true
  | unchanged _ = false;


(*---------------------------------------------------------------------------
 * Support for rewriting with congruence rules.
 *---------------------------------------------------------------------------*)

fun variants away0 vlist =
  rev(fst (rev_itlist (fn v => fn (V,away) =>
             let val v' = variant away v in (v'::V, v'::away) end)
           vlist ([],away0)));

fun variants_theta away0 vlist =
 rev_itlist (fn v => fn (V,away) =>
    let val v' = variant away v
    in if aconv v v' then (V,away) else ((v|->v')::V, v'::away) end)
 vlist ([],away0);

fun rename_forall_prefix frees tm =
 let val (vs,t) = strip_forall tm
     val theta = fst (variants_theta frees vs)
 in
   list_mk_forall(map (subst theta) vs, subst theta t)
 end

(*---------------------------------------------------------------------------
 * Takes a list of free variables and a list of pairs. If any of
 * the free variables are in the pairs, they are replaced in the pairs
 * by variants.  The final pairs are returned.
 *---------------------------------------------------------------------------*)

fun vstrl_variants away0 vstrl =
  let val fvl = free_varsl vstrl
      val clashes = op_intersect aconv away0 fvl
  in if null clashes then vstrl
     else let val theta =
               #1(rev_itlist (fn v => fn (theta, pool) =>
                     let val v' = variant pool v
                     in
                       if aconv v v' then (theta,pool)
                       else ((v|->v')::theta, v'::pool)
                     end) clashes ([], op_union aconv away0 fvl))
          in map (subst theta) vstrl
          end
  end;

fun thml_fvs thl =
   Lib.op_U aconv (map (fn th => let val (asl,c) = dest_thm th
                                 in free_varsl (c::asl)
                                 end) thl);
val dest_combn = let
  fun dest acc tm 0 = (tm,acc)
    | dest acc tm n =
       let val (M,N) = dest_comb tm
       in dest (N::acc) M (n-1)
       end handle _ => raise ERR "dest_combn" ""
  in
    dest []
  end

(*---------------------------------------------------------------------------*)
(* A congruence rule can have two kinds of antecedent: universally           *)
(* quantified or unquantified. A bare antecedent is fairly simple to deal    *)
(* with: it has the form                                                     *)
(*                                                                           *)
(*    conditions ==> lhs = ?rhs                                              *)
(*                                                                           *)
(* The following congruence rule has only bare antecedents:                  *)
(*                                                                           *)
(*    |- !P Q x x' y y'.                                                     *)
(*           (P ⇔ Q) /\                                                  UOK *)
(*           (Q ⇒ (x = x')) /\                                           UOK *)
(*           (¬Q ⇒ (y = y'))                                             UOK *)
(*           ==>                                                             *)
(*           ((if P then x else y) = if Q then x' else y')                   *)
(*                                                                           *)
(* A bare antecedent is processed by assuming the conditions and rewriting   *)
(* the LHS of the equation. This yields the value for ?rhs.                  *)
(*                                                                           *)
(* A quantified antecedent is more troublesome, since it usually implies     *)
(* that something higher-order is going on, and so beta-conversion and       *)
(* paired-lambdas may need to be handled. The following is the congruence    *)
(* rule for LET:                                                             *)
(*                                                                           *)
(*  |- (M = M') /\ (!x. (x = M') ==> (f x = g x)) ==> LET f M = LET g M'     *)
(*                                                                           *)
(* In the second antecedent, f is a function that may for example be a       *)
(* constant, a lambda term, a paired lambda term, or even the application    *)
(* of a higher order function. In order to extract termination conditions    *)
(* from f x, a (paired) beta reduction will be done, giving                  *)
(*                                                                           *)
(*     |- f x = t                                                            *)
(*                                                                           *)
(* and then extraction proceeds on t, giving                                 *)
(*                                                                           *)
(*   x = M', A |- t = t1                                                     *)
(*                                                                           *)
(* After extraction, a corresponding function g is obtained from t1. Since   *)
(* t1 may not be a lambda term, there may be a step of "un-beta-expansion"   *)
(* to obtain g = \x. t1.                                                     *)
(*                                                                           *)
(* Note.                                                                     *)
(* When doing rewriting of quantified antecedents to congruence rules, as    *)
(* in the one for "let" statements above, the temptation is there to only    *)
(* rewrite (in context) f to g, and use MK_COMB to get f x = g x. (Assume    *)
(* that f is a lambda term.) However, the free variables in the context      *)
(* (i.e., x) map to bound variables in f and the attempt to abstract on the  *)
(* way out of the rewrite will fail, or isolate the free variables. Dealing  *)
(* with this is the source of much complexity                                *)
(*                                                                           *)
(* Note.                                                                     *)
(* Context gets pushed and popped in stack fashion. When an element e of the *)
(* context Gamma gets popped, e is used to form the antecedent of a formula  *)
(* fm. If we are in the quantified (complex) case fm is universally          *)
(* quantified a few steps later. Problem: unless care is taken, it could be  *)
(* that, after popping e, there are remaining elements of Gamma that share   *)
(* free variables with e, and so the desired universal quantification of fm, *)
(* via generalization (fm is a theorem) will fail. Solution: the original    *)
(* antecedent has to be alpha-renamed so that no variable in the universal   *)
(* prefix is free in Gamma. Since the algorithm is going top-down, Gamma     *)
(* gets augmented in the descent. Thus each cong rule application in the     *)
(* traversal will have its local context addition renamed away from the      *)
(* variables above.                                                          *)
(*---------------------------------------------------------------------------*)

fun map2_total f (h1::t1) (h2::t2) = f h1 h2 :: map2_total f t1 t2
  | map2_total f other wise = [];

fun push_context L {simpls,context,prover} =
 let open HOLPP in
   lztrace(6,"push_context", fn () =>
    if null L then
      ppstring add_string "<no context to push>"
    else ppstring pp_terms L)
  ;
   {context = map ASSUME L @ context,
    simpls = simpls, prover = prover}
 end

fun pop_context L th =
 let open HOLPP in
    lztrace(6,"pop_context", fn () =>
      if null L then
        ppstring add_string "<no context to pop>"
      else ppstring pp_terms L)
   ;
    itlist DISCH L th
 end

fun no_change V L tm =
  NO_CHANGE (itlist GEN V (pop_context L (REFL tm)))

(*---------------------------------------------------------------------------*)
(* Applied to every antecedent that is not universally quantified.           *)
(*---------------------------------------------------------------------------*)

fun simple cnv cps (ant,rst) =
  case total ((I##dest_eq) o strip_imp_only) ant
   of NONE (* Not an equality, so just assume *)
         => (CHANGE(ASSUME ant), rst)
    | SOME (L,(lhs,rhs)) =>
       let val outcome =
          if aconv lhs rhs then
            no_change [] L lhs
          else
            let val cps' = push_context L cps
            in CHANGE(cnv cps' lhs)
               handle HOL_ERR _ => no_change [] L lhs
                    | UNCHANGED => no_change [] L lhs
            end
       in
        case outcome
         of CHANGE th =>
              let val Mnew = boolSyntax.rhs(concl th)
                  val th' = pop_context L th
              in (CHANGE th', map (subst [rhs |-> Mnew]) rst)
              end
          | NO_CHANGE _ => (outcome, map (subst [rhs |-> lhs]) rst)
       end

(*---------------------------------------------------------------------------*)
(* Congruence rule antecedent of the form !vs. P vs ==> f vs = f' vs         *)
(* The f' is a variable found by recursively extracting from the beta-reduct *)
(* of "f vs". If f is a lambda term (\p1..pk. M[p1,...,pk]) where the pi can *)
(* be varstructs then                                                        *)
(*                                                                           *)
(*   vs = v1 .. vk v(k+1) .. vn                                              *)
(*      = vs1 @ vs2                                                          *)
(*                                                                           *)
(* In order to use the names given in the original recursion equations, we   *)
(* replace the vs1 variables by their corrresponding ps and rebuild the      *)
(* antecedent. Does this work?                                               *)
(*---------------------------------------------------------------------------*)

(*
fun complex cnv cps (ant,rst) =
  let val context_frees = free_varsl (map concl (#context cps))
    val (vlist,ceqn) = strip_forall ant
    val (l,r) = dest_eq (snd (strip_imp_only ceqn))
    val nvars = length (snd (strip_comb rhs))
    val (f,vs) = dest_combn l nvars
    val (user_vstructs,M) = strip_pabs f
    val nuvs = length user_vstructs
    val (vs1,vs2) = (List.take(vs,nuvs),List.drop(vs,nuvs))
*)

fun complex cnv cps (ant,rst) =
  let val context_frees = free_varsl (map concl (#context cps))
    val ant' = rename_forall_prefix context_frees ant
    val ant_frees = free_vars ant'
    val (vlist,ceqn) = strip_forall ant'
    val (_,eq) = strip_imp_only ceqn
    val (lhs,rhs) = dest_eq eq
    val (rhsFn,args) = strip_comb rhs
    val nvars = length args
    val f = fst(dest_combn lhs nvars)
    val vstrl = #1(strip_pabs f)
    val vstructs = vstrl_variants (op_union aconv ant_frees context_frees) vstrl

    (* Version of ant with user-given names (and tuple introduction) *)
    val ceqn' = if null vstrl then ceqn
                 else subst (map2_total (curry op|->) args vstructs) ceqn

    val (L,(lhs,rhs)) = (I##dest_eq) (strip_imp_only ceqn')
    (* TODO: we can't just push the context, since it can have
       beta-reducts that need to be unbeta'ed in order for this antecedent
       to be proved. *)
    val outcome =
       if aconv lhs rhs
        then no_change vlist L lhs
       else
       let val lhs_beta_maybe = Conv.QCONV (Conv.DEPTH_CONV GEN_BETA_CONV) lhs
           val lhs' = boolSyntax.rhs(concl lhs_beta_maybe)
           val cps' = push_context L cps
       in CHANGE(TRANS lhs_beta_maybe (cnv cps' lhs'))
          handle
            HOL_ERR _ =>
               if aconv lhs lhs' then
                 no_change vlist L lhs
               else CHANGE lhs_beta_maybe
          | UNCHANGED =>
               if aconv lhs lhs' then
                 no_change vlist L lhs
               else CHANGE lhs_beta_maybe
       end
  in
  case outcome
   of NO_CHANGE _ => (outcome, map (subst [rhsFn |-> f]) rst)
    | CHANGE th =>
      let (*------------------------------------------------------------*)
          (* Function eta_rhs packages up the new rhs, eta-expanding it *)
          (* if need be, i.e. if the lhs is an application of a lambda  *)
          (* or paired-lambda term f. In that case, the extraction has  *)
          (* first done a beta-reduction and then extraction, so the    *)
          (* derived rhs needs to be "un-beta-expanded" in order that   *)
          (* the existential var on the rhs (g)be filled in with a thing*)
          (* that has function syntax. This will allow the final        *)
          (* MATCH_MP icong ... to  succeed.                            *)
          (*------------------------------------------------------------*)
         fun drop n list =
             if n <= 0 orelse null list then list else drop (n-1) (tl list)

         (*-------------------------------------------------------------*)
         (* if fewer vstructs than args, this means that the body       *)
         (* (rcore below) has a function type and will be eta-expanded  *)
         (*-------------------------------------------------------------*)
         val pbeta_reductions = Int.min(length vstructs,length args)
         val rhs_arg_vstructs = snd (strip_comb rhs)
         (* At this point th has form

            A |- (\v1 ... vk. M [v1, ..., vk]) x1 ... xk x(k+1) ... xn
                 =
            M'[x1,...,xk] x(k+1) ... xn

           (1) If the head term of M' is not a lambda we expect

            A |- M x1 ... xn = M' x1 ... xn

           Note that the head term in this case could be a partial application,
           thus M x1 ... xi, i < n, might embody the new function. This is
           already handled. For the lambda case, we need to build something like

             (\v1 ... vk. M' [x1,...,xk |-> v1,...,vk]) x1 ... xn

           (2) M' is a lambda. Then all of the x1,..,xn have been consumed,
           and we don't have to do any special processing, just make

             (\x1 ... xn. M' [x1,...,xn]) x1 ... xn
         *)

         fun eta_rhs th =
           let val r = boolSyntax.rhs(concl th)
               val (f', f'app) =
                   if null vstrl then (* f is not a lambda term *)
                     let val (rcore,end_vars) = dest_combn r nvars
                         val f' = list_mk_pabs(vstructs,rcore)
                     in (f',list_mk_comb(f',vstructs@end_vars))
                     end else
                  if is_pabs r then (* all args consumed, maybe some vstructs left *)
                    let val etas = List.take(vstructs, pbeta_reductions)
                         val f' = list_mk_pabs(etas,r)
                     in
                       (f',list_mk_comb(f',rhs_arg_vstructs))
                     end
                  else  (* a pabs-headed comb, but not all args consumed *)
                  let val (rcore,end_vars) = dest_combn r (nvars - length vstrl)
                      val f' = list_mk_pabs(vstructs,rcore)
                  in (f',list_mk_comb(f',vstructs@end_vars))
                  end
               val rhs_eq =
                  if null vstrl then
                    REFL f'app
                  else SYM(Conv.QCONV (DEPTH_CONV GEN_BETA_CONV) f'app)

               val th1 = TRANS th rhs_eq (* |- f vstructs = f' vstructs *)
                         handle HOL_ERR _ => th
            in (f',th1)
            end

         val (f',th1) = eta_rhs th
         val th2 = pop_context L th1
         val unconsumed = drop (length vstructs) args
         val vstructs' = vstructs @ unconsumed
         val pairs = zip args vstructs' handle HOL_ERR _ => []
(*         val pairs = zip args vstructs handle HOL_ERR _ => [] *)

         fun genfail vs th =
            case op_intersect term_eq (free_varsl vs) (free_varsl (hyp th))
             of [] => ()
              | overlaps =>
                lztrace(6,"complex: ... FAILED generalization step", fn () =>
                String.concat [" variable(s)\n ",
                 ppstring pp_term (pairSyntax.list_mk_pair overlaps),
                 "\n to be generalized occur free in assums of antecedent theorem: \n",
                 Lib.with_flag(show_assums, true) (ppstring pp_thm) th, "\n\n"])

         fun generalize v thm =
            (case op_assoc1 aconv v pairs
              of SOME tup => pairTools.PGEN v tup thm
               | NONE => GEN v thm)
            handle e => (genfail [v] thm; raise e)

         val th3 = itlist generalize vlist th2
      in
        (CHANGE th3, map (subst [rhsFn |-> f']) rst)
      end
  end
  handle HOL_ERR _ => raise EXTRACTION_ERROR (#context cps, ant)

 (* complex *)

(* NB: any HOL_ERR exception being raised in try_cong will get
   trapped in SUB_QCONV and then recursion into subterms will
   be attempted. Will need an uncatchable exception!

  TODO: check that all congs added to cong rules DB are in right form:
    ant1 /\ ... /\ antn ==> fn vbar = fn vbar'
 *)
fun try_cong cnv cps tm =
 let val icong = CONG_STEP (#simpls cps) tm
  val ants = strip_conj (fst (dest_imp (concl icong)))
  val _ = lztrace(6,"Congruence Step", fn () =>
    String.concat ["\n", ppstring pp_thm icong])

  (* loop proves each antecedent in turn and propagates
     instantiations to the remainder. *)
  fun loop [] = []
    | loop (ant::rst) =
      let val _ = lztrace(6,"Congruence antecedent\n",
              fn () => ppstring pp_term ant)
          val (outcome,rst') =
           if is_forall ant
             then complex cnv cps (ant,rst)
             else simple cnv cps (ant,rst)
      in
        outcome::loop rst'
      end
  val outcomes = loop ants
  fun dest_change (NO_CHANGE th) = th
    | dest_change (CHANGE th) = th
 in
   if Lib.all unchanged outcomes
     then raise UNCHANGED
     else
     let val ant_conj_thm = LIST_CONJ (map dest_change outcomes)
         val _ = lztrace(6,"Proven congruence antecedents\n",
                 fn () => ppstring pp_thm ant_conj_thm)
     in
       MATCH_MP icong ant_conj_thm  (* should not fail *)
     end
 end

fun SUB_QCONV cnv cps tm =
 case dest_term tm
  of COMB(Rator,Rand) =>
      (try_cong cnv cps tm
       handle UNCHANGED => raise UNCHANGED
          | HOL_ERR _ =>
              let val th = cnv cps Rator
              in MK_COMB (th, cnv cps Rand) handle UNCHANGED => AP_THM th Rand
              end
              handle UNCHANGED => AP_TERM Rator (cnv cps Rand)
      )
   | LAMB(Bvar,Body) =>
      let val Bth = cnv cps Body
      in ABS Bvar Bth
         handle HOL_ERR _ =>
          let val _ = lztrace(6, "SUB_QCONV",
                              trace ("assumptions", 1)
                              (fn () => "ABS failure: " ^
                                        ppstring pp_term Bvar ^ "  " ^
                                        ppstring pp_thm Bth))
              val v = genvar (type_of Bvar)
              val th1 = ALPHA_CONV v tm
              val call2 = cnv cps (body(rhs(concl th1)))
              val _ = lztrace(6, "SUB_QCONV",
                              trace ("assumptions", 1)
                              (fn () => "ABS 2nd call: "^
                                        ppstring pp_thm call2))
              val eq_thm' = ABS v call2
              val at = snd(dest_eq(concl eq_thm'))
              val v' = variant (free_vars at) Bvar
              val th2 = ALPHA_CONV v' at
          in TRANS (TRANS th1 eq_thm') th2
          end
      end
   | otherwise => raise UNCHANGED     (* Constants and  variables *)


fun RE_EXTRACT_QCONV cps tm =
 THENQC
   (REPEATQC RW_STEP)
   (TRY_QCONV
       (THENQC (CHANGED_QCONV (SUB_QCONV RE_EXTRACT_QCONV))
               (TRY_QCONV (THENQC RW_STEP RE_EXTRACT_QCONV))))
  cps tm;

fun EXTRACT_QCONV cps tm =
   TRY_QCONV (ORELSEQC RW_STEP (SUB_QCONV EXTRACT_QCONV)) cps tm;


(*---------------------------------------------------------------------------
         Capturing termination conditions.
 ----------------------------------------------------------------------------*)

local fun !!v M = mk_forall(v, M)
      val mem = Lib.op_mem aconv
      fun set_diff a b = Lib.filter (fn x => not (mem x b)) a
in
fun capture (restrf,f,G,nref) context tm =
  let val globals = f::G  (* not to be generalized *)
      fun genl tm = itlist !! (set_diff (rev(free_vars tm)) globals) tm
      val rcontext = rev context
      val antl =
         case rcontext
           of [] => []
            | _  => [list_mk_conj(map concl rcontext)]
      val TC = genl(list_mk_imp(antl, tm))
      val (R,arg,pat) = wfrecUtils.dest_relation tm
  in
     if can(find_term (aconv restrf)) arg
     then (nref := true; raise ERR "solver" "nested function")
     else let val _ = if can(find_term (aconv f)) TC
                      then nref := true else ()
          in case rcontext
              of [] => SPEC_ALL(ASSUME TC)
               | _  => MATCH_MP (SPEC_ALL (ASSUME TC)) (LIST_CONJ rcontext)
          end
  end
end

(*---------------------------------------------------------------------------*)
(* TODO: repeatedly call EXTRACT_CONV for nested recursions.                 *)
(*---------------------------------------------------------------------------*)

fun extract FV congs (proto_def,WFR) =
 let val R = rand WFR
     val f = boolSyntax.lhs proto_def
     val CUT_LEM = ISPECL [f,R] relationTheory.RESTRICT_LEMMA
     val restr_fR = rator(rator(lhs(snd(dest_imp (concl (SPEC_ALL CUT_LEM))))))
     fun mk_restr p = mk_comb(restr_fR, p)
     val cut_simpls = add_rws empty_simpls [CUT_LEM]
     val init_simpls = add_congs cut_simpls congs
 in fn (p,th) =>
    let val nested_ref = ref false
        val FV' = FV@free_vars(concl th)
        val cps0 = {simpls = init_simpls,context = []:thm list,
                    prover = capture (mk_restr p, f, FV', nested_ref)}
(*        val th' = CONV_RULE (QCONV EXTRACT_QCONV cps0) th *)
        val th' = CONV_RULE (QCONV RE_EXTRACT_QCONV cps0) th
    in
      (th', Lib.op_set_diff aconv (hyp th') [proto_def,WFR], !nested_ref)
    end
end;

val _ = Parse.temp_set_grammars ambient_grammars;

end
