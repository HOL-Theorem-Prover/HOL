(*----------------------------------------------------------------------------
 * Rewriting splits into two parts:
 *
 *    1. Rewriting a subterm (M) by a set of rewrite rules. Conceptually,
 *       we choose the first rewrite rule that matches M
 *
 *           R = |- lhs = rhs
 *
 *       from the set, and instantiate to get
 *
 *           R' = |- M = rhs'.
 *
 *    2. Traversing the term. For a contextual rewriter, like this one, this
 *       involves adding new context at each node that introduces context
 *       (like a conditional statement).
 *--------------------------------------------------------------------------*)

structure RW :> RW =
struct

open HolKernel Parse boolLib pairLib;

val RW_ERR = mk_HOL_ERR "RW";

val monitoring = ref 0

val _ = register_trace ("TFL rewrite monitoring", monitoring, 20);

fun lztrace(i,fname,msgf) = if i <= !monitoring then
                         Lib.say ("RW."^fname^": "^ msgf() ^ "\n")
                      else ()


(* Fix the grammar used by this file *)
val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars boolTheory.bool_grammars


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

 (*--------------------------------------------------------------------------
  * Support for constructing rewrite rule sets. The following routines
  * are attempts at providing "not too restrictive" checks for whether
  * a rewrite will loop or not. These have been arrived at by trial and
  * error, and  can certainly be improved!
  * A couple of old versions follow.
  *
  * fun embedded_in tm =
  *   let val head = #1(strip_comb tm)
  *   in if is_var head then can (find_term (aconv head)) else fn _ => false
  *   end;
  *
  * fun embedded_in tm =
  *   let val head = #1(strip_comb tm)
  *   in if is_var head then can (find_term (can (match_term tm)))
  *                     else fn _ => false
  *   end;
  *--------------------------------------------------------------------------*)

 fun alike head tm1 tm2 =
  aconv (#1 (strip_comb tm2)) head andalso can (match_term tm1) tm2;

 fun embedded1 tm =
  let val head = #1(strip_comb tm)
  in if is_var head then alike head tm else K false
  end;

 (* For changing the notion of a looping rewrite. *)

 val embedded_ref = ref embedded1;


 (*---------------------------------------------------------------------------
  * I could check that the lhs is not embedded in the rhs, but that wouldn't
  * allow me to unroll recursive functions.
  *--------------------------------------------------------------------------*)
 fun might_loop th =
    let val (ants,(lhs,rhs)) = (I##dest_eq)(strip_imp_only(concl th))
        val embedded_in = !embedded_ref
        val islooper = (aconv lhs rhs) orelse (exists (embedded_in lhs) ants)
    in if (islooper  andalso !monitoring > 0)
       then Lib.say ("excluding possibly looping rewrite:\n"
                     ^thm_to_string th^"\n\n")
       else ();
       islooper
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
  let val istrue = boolSyntax.T
      fun mk_rewrs th =
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
          if aconv tm istrue then [] else
          [EQT_INTRO th]
      end
      handle HOL_ERR _ => raise RW_ERR "mk_simpls" ""
  in
    filter (not o might_loop) o mk_rewrs
  end;

 fun mk_simplsl SPECer = flatten o map (mk_simpls SPECer);

 local val MK_FRESH = mk_simpls GSPEC_ALL        (* partly apply *)
       val MK_READABLE = mk_simpls SPEC_ALL      (* partly apply *)
 in
 fun MK_RULES_APART th = MK_FRESH (GEN_ALL th)
 and MK_RULES th = MK_READABLE (GEN_ALL th)
 end;


(* Tells whether to add context to the simplication set as term is traversed *)
datatype context_policy = ADD | DONT_ADD;


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
 => raise RW_ERR "add_rws" "Unable to deal with input";


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
  raise RW_ERR"add_congs" "Unable to deal with input"


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

fun stringulate _ [] = []
  | stringulate f [x] = [f x]
  | stringulate f (h::t) = f h::",\n"::stringulate f t;

val drop_opt = List.mapPartial Lib.I

local fun sys_var tm = (is_var tm andalso
                        not(Lexis.ok_identifier(fst(dest_var tm))))
      val failed = RW_ERR "RW_STEP" "all applications failed"
in
fun RW_STEP {context=(cntxt,_),prover,simpls as RW{rw_net,...}} tm = let
  fun match f =
      (case f tm of
         UNCOND th => SOME th
       | COND th => let
           val condition = fst(dest_imp(concl th))
           val cond_thm = prover simpls cntxt condition
          val ant_vars_fixed = not(can(find_term sys_var) condition)
         in
           SOME ((if ant_vars_fixed then MP else MATCH_MP) th cond_thm)
         end)
      handle HOL_ERR _ => NONE
  fun try [] = raise failed
    | try (f::rst) =
      case match f of
        NONE => try rst
      | SOME th =>
        if !monitoring > 0 then
          (set_trace "assumptions" 1;
           case drop_opt (map match rst) of
             [] => (Lib.say (String.concat
                                 ["RW_STEP:\n", Parse.thm_to_string th]);
                    th before set_trace "assumptions" 0)
           | L => (Lib.say (String.concat
                                ["RW_STEP: multiple rewrites possible \
                                 \(first taken):\n",
                                 String.concat
                                    (stringulate Parse.thm_to_string (th::L))]);
                   th before set_trace "assumptions" 0))
        else th
in
   try (Net.match tm rw_net)
end
end

(*---------------------------------------------------------------------------
 * It should be a mistake to have more than one applicable congruence rule for
 * a constant, but I don't currently check that.
 *---------------------------------------------------------------------------*)

fun CONG_STEP (RW{cong_net,...}) tm = Lib.trye hd (Net.match tm cong_net) tm;

(*----------------------------------------------------------------------------
 *                          Prettyprinting
 *---------------------------------------------------------------------------*)

local open Portable
in
fun pp_simpls ppstrm (RW{thms,congs,...}) =
   let val {add_string,add_break,begin_block,end_block,add_newline,...} =
         with_ppstream ppstrm
       val pp_thm = Parse.pp_thm ppstrm
       val thms' = mk_simplsl SPEC_ALL (rev(flatten thms))
       val congs' = rev(flatten congs)
       val how_many_thms = length thms'
       val how_many_congs = length congs'
   in
      begin_block PP.CONSISTENT 0;
      if (how_many_thms = 0)
      then (add_string "<empty simplification set>")
      else ( add_string"Rewrite Rules:"; add_newline();
             add_string"--------------"; add_newline();
             begin_block PP.INCONSISTENT 0;
             pr_list pp_thm (fn () => add_string";")
                            (fn () => add_break(2,0))
                            thms';
             end_block());
      add_newline();
      add_string("Number of rewrite rules = "^Lib.int_to_string how_many_thms);
      add_newline();
      if (how_many_congs = 0)
      then ()
      else (add_newline();
            add_string"Congruence Rules"; add_newline();
            add_string"----------------"; add_newline();
            begin_block PP.CONSISTENT 0;
            pr_list pp_thm (fn () => add_string";")
                           (fn () => add_break(2,0))
                           congs';
            end_block();
            add_newline();
            add_string("Number of congruence rules = "
                       ^Lib.int_to_string how_many_congs);
            add_newline());

      end_block()
   end
end;

fun join_simpls s1 s2 =
   let val {rws,congs,...} = dest_simpls s1
   in add_congs (add_rws s2 rws) congs
   end;

 (* end implementation of simpls type *)

val std_simpls = add_rws empty_simpls
 ([boolTheory.REFL_CLAUSE,
   boolTheory.EQ_CLAUSES,
   boolTheory.NOT_CLAUSES,
   boolTheory.AND_CLAUSES,
   boolTheory.OR_CLAUSES,
   boolTheory.IMP_CLAUSES,
   boolTheory.COND_CLAUSES,
   boolTheory.FORALL_SIMP,
   boolTheory.EXISTS_SIMP,
   boolTheory.ABS_SIMP]
 @
   [Q.prove(`(!x:'a. ?y. x = y) /\ !x:'a. ?y. y = x`,
     CONJ_TAC THEN GEN_TAC THEN EXISTS_TAC(Term`x:'a`) THEN REFL_TAC)]);

(*----------------------------------------------------------------------------
 *
 *                             TERM TRAVERSAL
 *
 *---------------------------------------------------------------------------*)

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

local val CHANGED_QRW_ERR = RW_ERR "CHANGED_QRW" ""
in
fun CHANGED_QCONV cnv cp tm =
   let val th = cnv cp tm handle UNCHANGED => raise CHANGED_QRW_ERR
       val (lhs,rhs) = dest_eq (concl th)
   in if aconv lhs rhs then raise CHANGED_QRW_ERR else th
   end
end;

fun TRY_QCONV cnv = ORELSEQC cnv ALL_QCONV;

datatype delta = CHANGE of thm | NO_CHANGE of thm;

fun unchanged (NO_CHANGE _) = true | unchanged _ = false;


(*---------------------------------------------------------------------------
 * And now, a whole bunch of support for rewriting with congruence rules.
 *---------------------------------------------------------------------------*)

fun variants away0 vlist =
  rev(fst (rev_itlist (fn v => fn (V,away) =>
             let val v' = variant away v in (v'::V, v'::away) end)
           vlist ([],away0)));

fun variant_theta away0 vlist =
 rev_itlist (fn v => fn (V,away) =>
    let val v' = variant away v
    in if aconv v v' then (V,away) else ((v|->v')::V, v'::away) end)
 vlist ([],away0);

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

fun dest_combn tm 0 = (tm,[])
  | dest_combn tm n =
     let val (Rator,Rand) = dest_comb tm
         val (f,rands) = dest_combn Rator (n-1)
     in (f,Rand::rands)
     end;

fun add_cntxt ADD = add_rws | add_cntxt DONT_ADD = Lib.K;

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
(* In the second antecedent, f is a function that may be a constant, a       *)
(* lambda term, a paired lambda term, or even the application of a higher-   *)
(* order function. In order to extract termination conditions from f x,      *)
(* a (paired) beta reduction will be done, which can completely transform    *)
(* the term structure. After extraction, a corresponding function g is       *)
(* obtained from the rhs of the equality theorem returned. This may not look *)
(* like a function, so there is a step of "un-beta-expansion" on g.          *)
(*                                                                           *)
(* Note.                                                                     *)
(* When doing rewriting of quantified antecedents to congruence rules, as    *)
(* in the one for "let" statements above, the temptation is there to only    *)
(* rewrite (in context) f to g, and use MK_COMB to get f x = g x. (Assume    *)
(* that f is a lambda term.) However, the free variables in the context      *)
(* (i.e., x) map to bound variables in f and the attempt to abstract on the  *)
(* way out of the rewrite will fail, or isolate the free variables. Dealing  *)
(* with this causes some clutter in the code.                                *)
(*---------------------------------------------------------------------------*)

fun no_change V L tm =
  NO_CHANGE (itlist GEN V (itlist DISCH L (REFL tm)))

fun map2_total f (h1::t1) (h2::t2) = f h1 h2 :: map2_total f t1 t2
  | map2_total f other wise = [];

fun try_cong cnv (cps as {context,prover,simpls}) tm =
 let
 fun simple cnv (cps as {context as (cntxt,b),prover,simpls}) (ant,rst) =
   case total ((I##dest_eq) o strip_imp_only) ant
    of NONE (* Not an equality, so just assume *)
         => (CHANGE(ASSUME ant), rst)
     | SOME (L,(lhs,rhs))
        => let val outcome =
             if aconv lhs rhs then no_change [] L lhs
             else let val cps' = if null L then cps else
                          {context = (map ASSUME L @ cntxt,b),
                           prover  = prover,
                           simpls  = add_cntxt b simpls (map ASSUME L)}
                  in CHANGE(cnv cps' lhs)
                     handle HOL_ERR _ => no_change [] L lhs
                          | UNCHANGED => no_change [] L lhs
                  end
           in
        case outcome
         of CHANGE th =>
              let val Mnew = boolSyntax.rhs(concl th)
              in (CHANGE (itlist DISCH L th),
                  map (subst [rhs |-> Mnew]) rst)
              end
          | NO_CHANGE _ => (outcome, map (subst [rhs |-> lhs]) rst)
        end

 fun complex cnv (cps as {context as (cntxt,b),prover,simpls}) (ant,rst) =
  let val ant_frees = free_vars ant
    val context_frees = free_varsl (map concl cntxt)
    val (vlist,ceqn) = strip_forall ant
    val (L0,eq) = strip_imp_only ceqn
    val (lhs,rhs) = dest_eq eq
    val nvars = length (snd (strip_comb rhs))  (* guessing ... *)
    val (f,args) = (I##rev) (dest_combn lhs nvars)
    val (rhsv,_) = dest_combn rhs nvars
    val vstrl = #1(strip_pabs f)
    val vstructs = vstrl_variants (op_union aconv ant_frees context_frees) vstrl
    val ceqn' = if null vstrl then ceqn else subst (map (op|->) (zip args vstructs)) ceqn

(*    val ceqn' = if null vstrl then ceqn
                 else subst (map2_total (curry op|->) args vstructs) ceqn
*)

    val (L,(lhs,rhs)) = (I##dest_eq) (strip_imp_only ceqn')
    val outcome =
       if aconv lhs rhs
        then no_change vlist L lhs
       else
       let val lhs_beta_maybe = Conv.QCONV (Conv.DEPTH_CONV GEN_BETA_CONV) lhs
           val lhs' = boolSyntax.rhs(concl lhs_beta_maybe)
           val cps' = case L
                       of [] => cps
                        | otherwise =>
                            {context = (map ASSUME L @ cntxt,b),
                             prover = prover,
                             simpls  = add_cntxt b simpls (map ASSUME L)}
       in CHANGE(TRANS lhs_beta_maybe (cnv cps' lhs'))
          handle HOL_ERR _ =>
                  if aconv lhs lhs'
                    then no_change vlist L lhs
                    else CHANGE lhs_beta_maybe
               | UNCHANGED => if aconv lhs lhs'
                              then no_change vlist L lhs
                              else CHANGE lhs_beta_maybe
       end
  in
  case outcome
   of NO_CHANGE _ => (outcome, map (subst [rhsv |-> f]) rst)
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
            if n <= 0 orelse null list then list
            else drop (n-1) (tl list)
         (*-------------------------------------------------------------*)
         (* if fewer vstructs than args, this means that the body       *)
         (* (rcore below) has a function type and will be eta-expanded  *)
         (*-------------------------------------------------------------*)
         val unconsumed = drop (length vstructs) args
         val vstructs' = vstructs @ unconsumed
         fun eta_rhs th =
           let val r = boolSyntax.rhs(concl th)
               val not_lambda_app = null vstrl
               val rcore = if not_lambda_app
                            then fst(dest_combn r nvars)
                            else r
(*               val g = list_mk_pabs(vstructs',rcore)
               val gvstructs = list_mk_comb(g,vstructs')
*)
               val g = list_mk_pabs(vstructs,rcore)
               val gvstructs = list_mk_comb(g,vstructs)

               val rhs_eq = if not_lambda_app then REFL gvstructs
                            else SYM(Conv.QCONV (DEPTH_CONV GEN_BETA_CONV) gvstructs)
               val th1 = TRANS th rhs_eq (* |- f vstructs = g vstructs *)
                         handle HOL_ERR _ => th
            in (g,th1)
            end
         val (g,th1) = eta_rhs th
         val th2 = itlist DISCH L th1
(*         val pairs = zip args vstructs' handle HOL_ERR _ => [] *)
         val pairs = zip args vstructs handle HOL_ERR _ => []
         fun generalize v thm =
              case op_assoc1 aconv v pairs
               of SOME tup => pairTools.PGEN v tup thm
                | NONE => GEN v thm
          val result = itlist generalize vlist th2
      in
        (CHANGE result, map (subst [rhsv |-> g]) rst)
      end
  end (* complex *)

  val icong = CONG_STEP simpls tm
  val ants = strip_conj (fst(dest_imp (concl icong)))
  (* loop proves each antecedent in turn and propagates
     instantiations to the remainder. *)
  fun loop [] = []
    | loop (ant::rst) =
      let val (outcome,rst') =
           if is_forall ant
             then complex cnv cps (ant,rst)
             else simple cnv cps (ant,rst)
      in
        outcome::loop rst'
      end
  val outcomes = loop ants
  fun mk_ant (NO_CHANGE th) = th
    | mk_ant (CHANGE th) = th
 in
   if Lib.all unchanged outcomes
     then raise UNCHANGED
     else MATCH_MP icong (LIST_CONJ (map mk_ant outcomes))
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


fun DEPTH_QCONV cnv cps tm =
   THENQC (SUB_QCONV (DEPTH_QCONV cnv)) (REPEATQC cnv) cps tm;

fun REDEPTH_QCONV cnv cps tm =
   THENQC
     (SUB_QCONV (REDEPTH_QCONV cnv))
     (ORELSEQC (THENQC cnv (REDEPTH_QCONV cnv)) ALL_QCONV)
     cps tm;

fun TOP_DEPTH_QCONV cnv cps tm =
 THENQC
   (REPEATQC cnv)
   (TRY_QCONV
       (THENQC (CHANGED_QCONV (SUB_QCONV (TOP_DEPTH_QCONV cnv)))
               (TRY_QCONV (THENQC cnv (TOP_DEPTH_QCONV cnv)))))
  cps tm;

fun ONCE_DEPTH_QCONV cnv cps tm =
   TRY_QCONV (ORELSEQC cnv (SUB_QCONV (ONCE_DEPTH_QCONV cnv))) cps tm;


type cntxt_solver = {context:thm list * context_policy,
                     simpls:simpls,
                     prover:simpls -> thm list -> term -> thm};

type strategy = (cntxt_solver -> term -> thm) -> (cntxt_solver -> term -> thm)

(* strategy builders *)

fun DEPTH x = QCONV (DEPTH_QCONV x);
fun REDEPTH x = QCONV (REDEPTH_QCONV x);
fun TOP_DEPTH x = QCONV (TOP_DEPTH_QCONV x);
fun ONCE_DEPTH x = QCONV (ONCE_DEPTH_QCONV x);

fun RAND f cntxt tm =
   let val (Rator,Rand) = dest_comb tm
   in AP_TERM Rator (f cntxt Rand)
   end
   handle HOL_ERR _ => raise RW_ERR "RAND" ""

fun RATOR f cntxt tm =
   let val (Rator,Rand) = dest_comb tm
   in AP_THM (f cntxt Rator) Rand
   end
   handle HOL_ERR _  => raise RW_ERR "RATOR" ""

fun ABST f cntxt tm =
   let val (Bvar,Body) = dest_abs tm
   in ABS Bvar (f cntxt Body)
   end
   handle HOL_ERR _ => raise RW_ERR "ABST" "";


(*---------------------------------------------------------------------------*
 * This is the basis for all the high-level rewriting entrypoints. Basically,*
 * the simpls get computed and after that the traverser moves around the     *
 * term and applies RW_STEP at nodes.                                        *
 *---------------------------------------------------------------------------*)

fun RW_STEPS traverser (simpls,context,congs,prover) thl =
   let val simpls' = add_congs(add_rws simpls thl) congs
   in
      traverser RW_STEP {context=context, prover=prover, simpls=simpls'}
   end;

(*---------------------------------------------------------------------------*
 * Define an implicit set of rewrites, so that common rewrite rules don't    *
 * need to be constantly given by the user.                                  *
 *---------------------------------------------------------------------------*)

local val implicit = ref std_simpls
in
   fun implicit_simpls() = !implicit
   fun set_implicit_simpls rws = (implicit := rws)
end

val add_implicit_rws = fn thl => set_implicit_simpls
                                       (add_rws (implicit_simpls()) thl)
val add_implicit_congs = fn thl => set_implicit_simpls
                                       (add_congs(implicit_simpls()) thl)
val add_implicit_simpls = fn s => set_implicit_simpls
                                       (join_simpls s (implicit_simpls()))

datatype repetitions
          = Once
          | Fully
          | Special of strategy;

datatype rules
          = Default of thm list
          | Pure of thm list
          | Simpls of simpls * thm list

datatype context = Context of thm list * context_policy
datatype congs   = Congs of thm list
datatype solver  = Solver of simpls -> thm list -> term -> thm;


(* Term rewriting *)

(*---------------------------------------------------------------------------
 * The basic choices are in the traversal strategy and whether or not to use
 * a default set of simplifications.
 *---------------------------------------------------------------------------*)

fun Rewrite Once (Simpls(ss,thl),Context cntxt,Congs congs,Solver solver) =
                 RW_STEPS ONCE_DEPTH (ss,cntxt,congs,solver) thl

 | Rewrite Fully (Simpls(ss,thl),Context cntxt,Congs congs,Solver solver) =
                 RW_STEPS TOP_DEPTH (ss,cntxt,congs,solver) thl

 | Rewrite(Special f)(Simpls(ss,thl),Context cntxt,Congs congs,Solver solver) =
                     RW_STEPS f (ss,cntxt,congs,solver) thl

 | Rewrite Once (Default thl,Context cntxt,Congs congs,Solver solver) =
                RW_STEPS ONCE_DEPTH (implicit_simpls(),
                                     cntxt,congs,solver) thl

 | Rewrite Once (Pure thl,Context cntxt,Congs congs,Solver solver) =
                RW_STEPS ONCE_DEPTH (empty_simpls,cntxt,congs,solver) thl

 | Rewrite Fully (Default thl,Context cntxt,Congs congs,Solver solver) =
                 RW_STEPS TOP_DEPTH(implicit_simpls(),
                                    cntxt,congs,solver) thl

 | Rewrite Fully (Pure thl,Context cntxt,Congs congs,Solver solver) =
                  RW_STEPS TOP_DEPTH (empty_simpls,cntxt,congs,solver) thl

 | Rewrite (Special f) (Default thl,Context cntxt,Congs congs,Solver solver) =
                 RW_STEPS f (implicit_simpls(),cntxt,congs,solver) thl

 | Rewrite (Special f) (Pure thl,Context cntxt,Congs congs,Solver solver) =
                       RW_STEPS f (empty_simpls,cntxt,congs,solver) thl;



(*---------------------------------------------------------------------------
 * Theorem rewriting
 *---------------------------------------------------------------------------*)

fun REWRITE_RULE style controls = CONV_RULE(Rewrite style controls);

fun add_hyps asl =
let val asl_thms = map ASSUME asl
    fun add (Simpls(ss,thl),Context(L,p),c,s) =
            (Simpls(ss, thl@asl_thms), Context(L@asl_thms,p),c,s)
      | add (Pure thl,Context(L,p),c,s) =
            (Pure(thl@asl_thms),Context(L@asl_thms,p),c,s)
      | add (Default thl,Context(L,p),c,s) =
            (Default(thl@asl_thms),Context(L@asl_thms,p),c,s)
in add
end

fun ASM_REWRITE_RULE style controls =
 fn th => REWRITE_RULE  style (add_hyps(hyp th) controls) th;


(*---------------------------------------------------------------------------
 * Goal rewriting
 *---------------------------------------------------------------------------*)

fun REWRITE_TAC style controls = CONV_TAC(Rewrite style controls);

fun ASM_REWRITE_TAC style controls =
  W(fn (asl,w) => REWRITE_TAC style (add_hyps asl controls));


(*---------------------------------------------------------------------------
 * Some solvers. One just does minor checking in the context; the other
 * makes a recursive invocation of the rewriter.
 *---------------------------------------------------------------------------*)

fun solver_err() = raise RW_ERR "solver error" "";
fun always_fails x y z = solver_err();

(*---------------------------------------------------------------------------
 * Just checks the context to see if it can find an instance of "tm".
 *---------------------------------------------------------------------------*)

fun std_solver _ context tm =
 let val _ = if !monitoring > 0
             then Lib.say("Solver: trying to lookup in context\n"
                          ^term_to_string tm^"\n") else ()
     fun loop [] = (if !monitoring > 0 then
                      Lib.say "Solver: couldn't find it.\n"
                    else ();
                    solver_err())
       | loop (x::rst) =
           let val c = concl x
           in if aconv c boolSyntax.F
              then CCONTR tm x
              else if aconv tm c then x
                   else INST_TY_TERM (Term.match_term c tm) x
                      handle HOL_ERR _ => loop rst
           end
     val thm = loop (boolTheory.TRUTH::context)
 in
    if !monitoring > 0 then Lib.say "Solver: found it.\n" else ();
    thm
 end;


(*---------------------------------------------------------------------------*
 * Make a recursive invocation of rewriting. Can be magically useful, but    *
 * also can loop. In which case, use the std_solver.                         *
 *---------------------------------------------------------------------------*)

fun rw_solver simpls context tm =
 let open boolSyntax
     val _ = if !monitoring > 0
             then Lib.say("Solver: attempting to prove (by rewriting)\n  "
                          ^term_to_string tm^"\n") else ()
     val th = TOP_DEPTH RW_STEP {context = (context,ADD),
                                  simpls = simpls,
                                  prover = rw_solver} tm
     val _ = if !monitoring > 0
             then let val (lhs,rhs) = dest_eq(concl th)
                  in if aconv rhs T
                     then Lib.say("Solver: proved\n"^thm_to_string th^"\n\n")
                     else Lib.say("Solver: unable to prove.\n\n")
                  end
             else ()
     val tm' = boolSyntax.rhs(concl th)
     fun loop [] = solver_err()
       | loop (x::rst) =
           let val c = concl x
           in if aconv c F then CCONTR tm x
              else if aconv tm' c then x
                   else INST_TY_TERM (Term.match_term c tm') x
                      handle HOL_ERR _ => loop rst
           end
 in EQ_MP (SYM th) (loop (boolTheory.TRUTH::context))
 end;


(*---------------------------------------------------------------------------*
 * The following are all instantiations of the above routines, to make them  *
 * easier to invoke. Some of these are holdovers from unconditional          *
 * rewriting and may not make a whole lot of sense. The "C" versions stand   *
 * for using context as rewrite rules, and proving conditions via            *
 * recursive invocations of the rewriter.                                    *
 *---------------------------------------------------------------------------*)

(* Rewrite a term *)

fun CRW_CONV thl = Rewrite Fully (Default thl,Context([],ADD),
                                  Congs[],Solver rw_solver)

fun RW_CONV thl = Rewrite Fully (Default thl,Context([],ADD),
                                 Congs[],Solver std_solver)

fun PURE_RW_CONV thl = Rewrite Fully (Pure thl,Context([],DONT_ADD),
                                      Congs[],Solver std_solver)
fun ONCE_RW_CONV thl = Rewrite Once
                               (Default thl,Context([],ADD),
                                Congs[],Solver std_solver)

fun PURE_ONCE_RW_CONV thl = Rewrite Once (Pure thl,Context([],DONT_ADD),
                                          Congs[],Solver std_solver);


(* Rewrite a theorem *)

fun CRW_RULE thl = REWRITE_RULE Fully (Default thl,Context([],ADD),
                                       Congs[],Solver rw_solver);
fun RW_RULE thl = REWRITE_RULE Fully (Default thl,Context([],ADD),
                                      Congs[],Solver std_solver);
fun ONCE_RW_RULE thl = REWRITE_RULE Once (Default thl,Context([],ADD),
                                          Congs[], Solver std_solver);
fun PURE_RW_RULE thl = REWRITE_RULE Fully (Pure thl,Context([],DONT_ADD),
                                           Congs[],Solver std_solver);
fun PURE_ONCE_RW_RULE thl = REWRITE_RULE Once (Pure thl,Context([],DONT_ADD),
                                               Congs[],Solver std_solver);


(* Rewrite a theorem with the help of its assumptions *)

fun ASM_CRW_RULE thl =
ASM_REWRITE_RULE Fully (Default thl,Context([],ADD),Congs[],Solver rw_solver);

fun ASM_RW_RULE thl =
ASM_REWRITE_RULE Fully (Default thl,Context([],ADD),Congs[],Solver std_solver);

fun ONCE_ASM_RW_RULE thl =
ASM_REWRITE_RULE Once (Default thl,Context([],ADD),Congs[],Solver std_solver);

fun PURE_ASM_RW_RULE thl =
ASM_REWRITE_RULE Fully (Pure thl,Context([],DONT_ADD),
                        Congs[],Solver std_solver);

fun PURE_ONCE_ASM_RW_RULE thl =
ASM_REWRITE_RULE Once (Pure thl,Context([],DONT_ADD),
                       Congs[],Solver std_solver);


(* Rewrite a goal *)

fun CRW_TAC thl =
REWRITE_TAC Fully (Default thl,Context([],ADD),Congs[],Solver rw_solver);

fun RW_TAC thl =
REWRITE_TAC Fully (Default thl,Context([],ADD),Congs[],Solver std_solver);

fun ONCE_RW_TAC thl =
REWRITE_TAC Once(Default thl,Context([],ADD),Congs[],Solver std_solver);

fun PURE_RW_TAC thl =
REWRITE_TAC Fully (Pure thl,Context([],DONT_ADD),Congs[],Solver std_solver);

fun PURE_ONCE_RW_TAC thl =
REWRITE_TAC Once (Pure thl,Context([],DONT_ADD), Congs[],Solver std_solver);


(* Rewrite a goal with the help of its assumptions *)

fun ASM_CRW_TAC thl =
ASM_REWRITE_TAC Fully (Default thl,Context([],ADD),Congs[],Solver rw_solver);

fun ASM_RW_TAC thl =
ASM_REWRITE_TAC Fully (Default thl,Context([],ADD),Congs[],Solver std_solver);

fun ONCE_ASM_RW_TAC thl =
ASM_REWRITE_TAC Once (Default thl,Context([],ADD),
                      Congs[],Solver std_solver);

fun PURE_ASM_RW_TAC thl =
ASM_REWRITE_TAC Fully (Pure thl,Context([],DONT_ADD),
                       Congs[],Solver std_solver);

fun PURE_ONCE_ASM_RW_TAC thl =
ASM_REWRITE_TAC Once (Pure thl,Context([],DONT_ADD),Congs[],Solver std_solver);

fun Simpl tac std_thms thl =
  let val pss = add_rws (implicit_simpls()) std_thms
      val RWTAC = REWRITE_TAC Fully (Simpls(pss,thl),Context([],ADD),
                                     Congs[],Solver std_solver)
  in RWTAC THEN TRY(CHANGED_TAC tac THEN RWTAC)
  end;

val _ = Parse.temp_set_grammars ambient_grammars;

end (* structure RW *)
