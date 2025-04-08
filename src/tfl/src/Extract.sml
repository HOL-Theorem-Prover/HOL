structure Extract :> Extract =
struct

open HolKernel Parse boolLib pairLib Rules;

val ERR = mk_HOL_ERR "Extract";

(* Fix the grammar used by this file *)
val ambient_grammars =
  Parse.current_grammars()
  before Parse.temp_set_grammars $ valOf $ grammarDB {thyname="bool"}

(* For debugging extraction failures *)
exception EXTRACTION_ERROR of term list * term

val monitoring = ref 0;
val max_trace_val = 5;
val no_trace = max_trace_val + 1;
val _ = register_trace ("TFL rewrite monitoring", monitoring, max_trace_val);

fun lztrace(i,title,msgf) =
  if i <= !monitoring then
     Lib.say (String.concat ["\n", title, msgf(), "\n"])
  else ()

fun indent_pp n pp =
 let open HOLPP String List
     val s = implode (tabulate (n,K #" "))
 in block INCONSISTENT 0 [add_string s, pp]
 end

fun pp_terms ts =
 let open HOLPP
 in block CONSISTENT 0 (pr_list pp_term [NL] ts)
 end

fun map2_total f (h1::t1) (h2::t2) = f h1 h2 :: map2_total f t1 t2
  | map2_total f other wise = [];

val dest_combn = let
  fun dest acc tm 0 = (tm,acc)
    | dest acc tm n =
       let val (M,N) = dest_comb tm
       in dest (N::acc) M (n-1)
       end handle _ => raise ERR "dest_combn" ""
  in
    dest []
  end

fun GSPEC_ALL th =
   (case dest_thy_const(rator (concl th))
     of {Name = "!",Thy="bool",Ty} =>
          GSPEC_ALL (SPEC (genvar (#1(dom_rng(#1(dom_rng Ty))))) th)
     | _ => th)
    handle HOL_ERR _ => th;

(*---------------------------------------------------------------------------*)
(* TC extraction is an application of conversions. The "simps" type supports *)
(* a simplification set having a single conditional rewrite rule, namely     *)
(* relationTheory.RESTRICT_LEMMA:                                            *)
(*                                                                           *)
(*   |- R y z ⇒ RESTRICT f R z y = f y                                       *)
(*                                                                           *)
(* along with a collection of congruence rules.                              *)
(*---------------------------------------------------------------------------*)

datatype simpls =
    RW of {thms     : thm list,
           congs    : thm list,
           rw_net   : (term -> thm) Net.net,
           cong_net : (term -> thm) Net.net};

val empty_simpls =
   RW{thms = [], congs = [],
      rw_net=Net.empty, cong_net=Net.empty}

(* TODO: check that all congs added to cong rules DB are in right form:
    ant1 /\ ... /\ antn ==> fn vbar = fn vbar'
 *)
fun CONGR th =
   let val (ants,eq) = strip_imp_only (concl th)
       val pat = lhs eq
       val matcher = Term.match_term pat
       fun match_then_inst tm =
          let val (tm_theta, ty_theta) = matcher tm
          in INST tm_theta (INST_TYPE ty_theta th) end
   in
     match_then_inst
   end

fun insert_congs (RW{cong_net, congs, thms, rw_net}) thl =
  RW{thms = thms, rw_net = rw_net,
     congs = thl @ congs,
     cong_net = itlist Net.insert
         (map (fn th =>
                let val c = concl th
                    val eq = snd(dest_imp c) handle HOL_ERR _ => c
                in
                   (lhs eq,  CONGR th)
                end)
              (map (GSPEC_ALL o GEN_ALL) thl))
         cong_net}
  handle HOL_ERR _ =>
  raise ERR "insert_congs" "Unable to deal with input"

fun simpls_of_congs congs = insert_congs empty_simpls congs;

fun CONG_STEP (RW{cong_net,...}) tm = Lib.trye hd (Net.match tm cong_net) tm;

fun insert_cut_lem (RW{thms,rw_net,congs, cong_net}) cut_lem =
  let val cut_lem' = GSPEC_ALL cut_lem
      val pat = lhs(snd(strip_imp_only(concl cut_lem')))
      val matcher = Term.match_term pat
      fun match_then_inst tm =
        let val (tm_theta, ty_theta) = matcher tm
        in INST tm_theta (INST_TYPE ty_theta cut_lem') end
  in
   RW{thms   = [cut_lem],
      congs  = congs,
    cong_net = cong_net,
      rw_net = Net.insert (pat, match_then_inst) rw_net}
  end

(*----------------------------------------------------------------------------
  In RW_STEP, we find the list of matching rewrites, and choose the first
  one that succeeds. But we only have a single, conditional, rule. The
  rule fires when the antecedent can be proved, and this is done by invoking
  the special "TC capture" prover (see the end of the present file) which
  packages up the termination conditions.
 *---------------------------------------------------------------------------*)

local
  fun sys_var tm =
     is_var tm andalso
     not (Lexis.is_clean_varname (fst (dest_var tm)))
in
fun RW_STEP {simpls as RW{rw_net,...},context,prover} tm =
 case Net.match tm rw_net
  of [matchFn] =>
     let val th = matchFn tm
        val condition = fst(dest_imp(concl th))
        val cond_thm = prover context condition
        val ant_vars_fixed = not(can(find_term sys_var) condition)
        val th1 = (if ant_vars_fixed then MP else MATCH_MP) th cond_thm
        val _ = if !monitoring <= 0 then ()
                else
                 (set_trace "assumptions" 1;
                  Lib.say (String.concat
                    ["\nTC Capture:\n", Parse.thm_to_string th1, "\n\n"]);
                  set_trace "assumptions" 0)
      in th1 end
   | otherwise => raise ERR "RW_STEP" ""
end

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

(*---------------------------------------------------------------------------*)
(* Name handling support                                                     *)
(*---------------------------------------------------------------------------*)

fun vary away v =
  let val v' = variant away v
  in if aconv v v' then (v,v::away) else (v',v'::away)
  end;

fun vary_theta v (theta,away) =
  let val v' = variant away v
  in if aconv v v' then (theta,away) else ((v|->v')::theta, v'::away)
  end

fun rename_forall_prefix frees =
 let fun variants_theta away0 vlist =
         rev_itlist vary_theta vlist ([],away0)
 in fn tm =>
  let val (vs,t) = strip_forall tm
      val theta = fst (variants_theta frees vs)
  in
   list_mk_forall(map (subst theta) vs, subst theta t)
 end end

(*---------------------------------------------------------------------------*)
(* Takes a list of free variables and a list of tuples, representing         *)
(* varstructs. If any of the free variables are in the tuples, they are      *)
(* replaced in the tuples by variants.                                       *)
(*---------------------------------------------------------------------------*)

fun variant_tuple away tuple =
 if is_var tuple then
     vary away tuple
 else
 if is_pair tuple then
   let val (p1,p2) = dest_pair tuple
       val (p1',away1) = variant_tuple away p1
       val (p2',away2) = variant_tuple away1 p2
   in (mk_pair(p1',p2'), away2)
   end

else
  (tuple,away)

fun vstruct_variants away vstructs =
  let fun iterFn vstruct (vstructs,away) =
        let val (vstruct',away') = variant_tuple away vstruct
        in (vstruct'::vstructs, away')
        end
  in
  itlist iterFn vstructs ([],away)
  end

(*---------------------------------------------------------------------------*)
(* For non-rewriter code interacting with the rewriter (which utilizes the   *)
(* UNCHANGED exception)                                                      *)
(*---------------------------------------------------------------------------*)

datatype delta
  = CHANGE of thm
  | NO_CHANGE of thm

fun unchanged (NO_CHANGE _) = true
  | unchanged _ = false;

fun dest_change (NO_CHANGE th) = th
  | dest_change (CHANGE th) = th

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
(*           (P ⇔ Q) /\                                                      *)
(*           (Q ⇒ (x = x')) /\                                               *)
(*           (¬Q ⇒ (y = y'))                                                 *)
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
(* variables in the existing context.                                        *)
(*---------------------------------------------------------------------------*)

fun push_context L {simpls,context,prover} =
 let open HOLPP
     val trace_level = if null L then no_trace else 2
 in
  lztrace(trace_level,"push_context:\n",
    fn () => ppstring (indent_pp 3 o pp_terms) L)
  ;
   {context = L @ context,
    simpls = simpls, prover = prover}
 end

fun pop_context L th =
 let open HOLPP
     val trace_level = if null L then no_trace else 4
 in
    lztrace(trace_level,"pop_context:\n  ", fn () => ppstring pp_terms L)
   ;
    itlist DISCH L th
 end

fun no_change V L tm =
  NO_CHANGE (itlist GEN V (pop_context L (REFL tm)))

(*---------------------------------------------------------------------------*)
(* Extraction on an antecedent that is not universally quantified.           *)
(*---------------------------------------------------------------------------*)

fun entering fname tm =
  lztrace(2, "Extracting from:\n\n",
      fn () => ppstring (indent_pp 3 o pp_term) tm)

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
                val _ = entering "simple" lhs
                val extracted = cnv cps' lhs
            in CHANGE extracted
            end
            handle HOL_ERR _ => no_change [] L lhs
                 | UNCHANGED => no_change [] L lhs
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
(* of "f vs". f can be a lambda term (\p1..pk. M[p1,...,pk]) where the pi    *)
(* can be varstructs. In order to use the names given in the original        *)
(* input, there is a step where v1...vk are replaced by the corrresponding   *)
(* p1,...,pk before extraction occurs. This has to be undone, ie, the pi are *)
(* replaced by the corresponding vi, in the last step of proving the         *)
(* antecedent.                                                               *)
(*---------------------------------------------------------------------------*)

fun complex cnv cps (ant,rst) =
  let val context_frees = free_varsl (#context cps)
    val ant' = rename_forall_prefix context_frees ant
    val ant_frees = Term.free_vars ant'
    val (vlist,ceqn) = strip_forall ant'
    val (_,eq) = strip_imp_only ceqn
    val (lhs,rhs) = dest_eq eq
    val (rhsFnVar,args) = strip_comb rhs
    val nargs = length args
    val lhsFn = fst(dest_combn lhs nargs)
    val vstructs =
       fst(vstruct_variants
             (op_union aconv ant_frees context_frees)
             (fst(strip_pabs lhsFn)))

    (* Adopt user-given names and introduce tuple args *)
    val theta = map2_total (curry op|->) args vstructs
    val ceqn' = subst theta ceqn
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
           fun nothing_extracted() = (* invoked post-extraction attempt *)
                if aconv lhs lhs' then
                   no_change vlist L lhs
                else CHANGE lhs_beta_maybe
       in
          let val cps' = push_context L cps
              val _ = entering "complex" lhs'
              val th1 = cnv cps' lhs'   (* recursively extract *)
              val th2 = TRANS lhs_beta_maybe th1
          in
             CHANGE th2
          end
          handle UNCHANGED => nothing_extracted()
               | HOL_ERR _ => nothing_extracted()
       end
  in
  case outcome
   of NO_CHANGE _ => (outcome, map (subst [rhsFnVar |-> lhsFn]) rst)
    | CHANGE th =>
      let (*------------------------------------------------------------*)
          (* Function unbeta_rhs packages up the new rhs,               *)
          (* beta-expanding it if need be, i.e. if lhsFn is an          *)
          (* application of a lambda or paired-lambda term f. In that   *)
          (* case, the extraction was preceded by a beta-reduction, so  *)
          (* the post-extraction rhs needs to be beta-expanded in order *)
          (* that rhsFnVar be filled in with a term that has function   *)
          (* syntax. This is needed for the final MATCH_MP icong to     *)
          (* succeed.                                                   *)
          (*------------------------------------------------------------*)
         val nbetas = Int.min(length vstructs,nargs)
         val rhs_args = snd (strip_comb rhs)

         fun unbeta_rhs th =
           let val r = boolSyntax.rhs(concl th)
               val (rhsFn, rhsFnapp) =
                  if null vstructs then (* lhsFn is not a lambda term *)
                     (fst(dest_combn r nargs),r)
                  else
                  let val fnbody =
                         if is_pabs r then r else fst(dest_combn r (nargs - nbetas))
                      val etas = List.take(vstructs, nbetas)
                      val rhsFn = list_mk_pabs(etas,fnbody)
                  in
                    (rhsFn,list_mk_comb(rhsFn,rhs_args))
                  end
               val rhs_eq =
                  if null vstructs then
                    REFL rhsFnapp
                  else SYM(Conv.QCONV (DEPTH_CONV GEN_BETA_CONV) rhsFnapp)

               val th1 = TRANS th rhs_eq (* |- lhsFn vstructs = rhsFn vstructs *)
            in
              (rhsFn,th1)
            end

         val (rhsFn,th1) = unbeta_rhs th
         val th2 = pop_context L th1

         fun generalize v thm =
            (case subst_assoc (aconv v) theta
              of SOME tup => pairTools.PGEN v tup thm
               | NONE => GEN v thm)

         val th3 = itlist generalize vlist th2
      in
        (CHANGE th3, map (subst [rhsFnVar |-> rhsFn]) rst)
      end
  end
  handle HOL_ERR _ => raise EXTRACTION_ERROR (#context cps, ant)
 (* complex *)

fun try_cong cnv cps tm =
 let val icong = CONG_STEP (#simpls cps) tm
  val _ = lztrace(4,"Congruence Step:\n", fn () => ppstring pp_thm icong)

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
  val ants = strip_conj (fst (dest_imp (concl icong)))
  val outcomes = loop ants
 in
   if Lib.all unchanged outcomes
     then raise UNCHANGED
     else
     let val ant_conj_thm = LIST_CONJ (map dest_change outcomes)
         val _ = lztrace(4,"All congruence antecedents proved\n",
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
            | _  => [list_mk_conj rcontext]
      val TC = genl(list_mk_imp(antl, tm))
      val (R,arg,pat) = wfrecUtils.dest_relation tm
  in
     if can(find_term (aconv restrf)) arg
     then (nref := true; raise ERR "solver" "nested function")
     else let val _ = if can(find_term (aconv f)) TC
                      then nref := true else ()
          in case rcontext
              of [] => SPEC_ALL(ASSUME TC)
               | _  => MATCH_MP (SPEC_ALL (ASSUME TC))
                                (LIST_CONJ (map ASSUME rcontext))
          end
  end
end

fun extract FV cong_simpls (proto_def,WFR) =
 let val R = rand WFR
     val f = boolSyntax.lhs proto_def
     val CUT_LEM = ISPECL [f,R] relationTheory.RESTRICT_LEMMA
     val restr_fR = rator(rator(lhs(snd(dest_imp (concl (SPEC_ALL CUT_LEM))))))
     val init_simpls = insert_cut_lem cong_simpls CUT_LEM
 in fn (p,th) =>
    let val _ = lztrace(3,"------------------------\nTC extraction on clause:\n\n",
                fn () => ppstring pp_term (concl th))
        val nested_ref = ref false
        val FV' = FV@free_vars(concl th)
        val cps0 = {simpls = init_simpls,context = []:term list,
                    prover = capture (mk_comb(restr_fR, p), f, FV', nested_ref)}
(*        val th' = CONV_RULE (QCONV EXTRACT_QCONV cps0) th *)
        val th' = CONV_RULE (QCONV RE_EXTRACT_QCONV cps0) th
    in
      (th', Lib.op_set_diff aconv (hyp th') [proto_def,WFR], !nested_ref)
    end
end;

val _ = Parse.temp_set_grammars ambient_grammars;

end
