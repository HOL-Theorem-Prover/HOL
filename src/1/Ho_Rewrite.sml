(* ===================================================================== *)
(* FILE          : Ho_Rewrite.sml                                        *)
(* DESCRIPTION   : Rewriting routines using higher-order matching. A     *)
(*                 straightforward adaptation of the first order         *)
(*                 rewriter found in Rewrite.sml.                        *)
(*                                                                       *)
(* AUTHOR        : Don Syme                                              *)
(* ===================================================================== *)


structure Ho_Rewrite :> Ho_Rewrite =
struct

open HolKernel boolTheory boolSyntax Abbrev
     Drule Conv Tactic Tactical Ho_Net;

type pred = term -> bool;

infix ## |->;

val ERR = mk_HOL_ERR "Ho_Rewrite";

val term_to_string = Parse.term_to_string;

(*-----------------------------------------------------------------------------
 * Split a theorem into a list of theorems suitable for rewriting:
 *
 *   1. Specialize all variables (SPEC_ALL).
 *
 *   2. Then do the following:
 *
 *        |- t1 /\ t2     -->    [|- t1 ; |- t2]
 *
 *   3. Then |- t --> |- t = T and |- ~t --> |- t = F
 *
 *---------------------------------------------------------------------------*)

fun mk_rewrites th =
  let val th = SPEC_ALL th
      val t = concl th
  in
  if is_eq t   then [th] else
  if is_conj t then (op @ o (mk_rewrites##mk_rewrites) o CONJ_PAIR) th else
  if is_neg t  then [EQF_INTRO th]
               else [EQT_INTRO th]
  end
  handle e => raise (wrap_exn "Ho_Rewrite" "mk_rewrites" e);


val monitoring = ref false;

val _ = register_btrace ("Ho_Rewrite", monitoring);

(*---------------------------------------------------------------------------
    A datatype of rewrite rule sets.
 ---------------------------------------------------------------------------*)

datatype rewrites = RW of {thms :thm list,  net :conv Ho_Net.net}

fun dest_rewrites(RW{thms, ...}) = thms

val empty_rewrites = RW{thms = [],  net = Ho_Net.empty}

val implicit = ref empty_rewrites;

fun add_rewrites (RW{thms,net}) thl =
  RW{thms = thms@thl,
     net = itlist Ho_Net.enter
     (map (fn th => (HOLset.listItems (hyp_frees th),
                     lhs(concl th), Conv.HO_REWR_CONV th))
	(itlist (append o mk_rewrites) thl [])) net}

fun implicit_rewrites() = #thms ((fn (RW x) => x) (!implicit));
fun set_implicit_rewrites thl = implicit := add_rewrites empty_rewrites thl;
fun add_implicit_rewrites thl = implicit := add_rewrites (!implicit) thl;

fun stringulate _ [] = []
  | stringulate f [x] = [f x]
  | stringulate f (h::t) = f h::",\n"::stringulate f t;


(*---------------------------------------------------------------------------
      Create a conversion from some rewrite rules
 ---------------------------------------------------------------------------*)

fun REWRITES_CONV (RW{net,...}) tm =
 if !monitoring
 then case mapfilter (fn f => f tm) (Ho_Net.lookup tm net)
       of []   => Conv.NO_CONV tm
        | [x]  => (HOL_MESG (String.concat
                    ["Rewrite:\n", Parse.thm_to_string x]) ; x)
        | h::t => (HOL_MESG (String.concat
           ["Multiple rewrites possible (first taken):\n",
            String.concat (stringulate Parse.thm_to_string (h::t))]); h)
 else Conv.FIRST_CONV (Ho_Net.lookup tm net) tm;

local open boolTheory
in
val _ = add_implicit_rewrites
   [REFL_CLAUSE, EQ_CLAUSES, NOT_CLAUSES, AND_CLAUSES,
    OR_CLAUSES, IMP_CLAUSES, FORALL_SIMP, EXISTS_SIMP,
    ABS_SIMP, SELECT_REFL, SELECT_REFL_2, COND_CLAUSES];
end;

(* =====================================================================*)
(* Main rewriting conversion                         			*)
(* =====================================================================*)

fun GEN_REWRITE_CONV' rw_func rws thl =
     rw_func (REWRITES_CONV (add_rewrites rws thl));

(* ---------------------------------------------------------------------*)
(* Rewriting conversions.                        			*)
(* ---------------------------------------------------------------------*)

val PURE_REWRITE_CONV      = GEN_REWRITE_CONV' TOP_DEPTH_CONV empty_rewrites
val PURE_ONCE_REWRITE_CONV = GEN_REWRITE_CONV' ONCE_DEPTH_CONV empty_rewrites
fun REWRITE_CONV thl       = GEN_REWRITE_CONV' TOP_DEPTH_CONV (!implicit) thl
fun ONCE_REWRITE_CONV thl  = GEN_REWRITE_CONV' ONCE_DEPTH_CONV (!implicit) thl
fun GEN_REWRITE_RULE f rws = CONV_RULE o GEN_REWRITE_CONV' f rws;
val PURE_REWRITE_RULE      = GEN_REWRITE_RULE TOP_DEPTH_CONV empty_rewrites
val PURE_ONCE_REWRITE_RULE = GEN_REWRITE_RULE ONCE_DEPTH_CONV empty_rewrites
fun REWRITE_RULE thl       = GEN_REWRITE_RULE TOP_DEPTH_CONV (!implicit) thl
fun ONCE_REWRITE_RULE thl  = GEN_REWRITE_RULE ONCE_DEPTH_CONV (!implicit) thl;

fun PURE_ASM_REWRITE_RULE L th = PURE_REWRITE_RULE((map ASSUME(hyp th))@L) th
fun PURE_ONCE_ASM_REWRITE_RULE L th =
    PURE_ONCE_REWRITE_RULE((map ASSUME(hyp th)) @ L) th
fun ASM_REWRITE_RULE thl th = REWRITE_RULE ((map ASSUME (hyp th)) @ thl) th
fun ONCE_ASM_REWRITE_RULE L th = ONCE_REWRITE_RULE((map ASSUME(hyp th))@ L) th

fun GEN_REWRITE_TAC f rws = CONV_TAC o GEN_REWRITE_CONV' f rws
val PURE_REWRITE_TAC = GEN_REWRITE_TAC TOP_DEPTH_CONV empty_rewrites
val PURE_ONCE_REWRITE_TAC = GEN_REWRITE_TAC ONCE_DEPTH_CONV empty_rewrites
fun REWRITE_TAC thl = GEN_REWRITE_TAC TOP_DEPTH_CONV (!implicit) thl
fun ONCE_REWRITE_TAC thl = GEN_REWRITE_TAC ONCE_DEPTH_CONV (!implicit) thl
fun PURE_ASM_REWRITE_TAC L = ASSUM_LIST (fn l => PURE_REWRITE_TAC (l @ L))
fun ASM_REWRITE_TAC thl = ASSUM_LIST (fn asl => REWRITE_TAC (asl @ thl))
fun PURE_ONCE_ASM_REWRITE_TAC L = ASSUM_LIST(fn l=>PURE_ONCE_REWRITE_TAC(l@L))
fun ONCE_ASM_REWRITE_TAC L  = ASSUM_LIST (fn l => ONCE_REWRITE_TAC (l @ L));

fun FILTER_PURE_ASM_REWRITE_RULE f thl th =
    PURE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
fun FILTER_ASM_REWRITE_RULE f thl th =
    REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
fun FILTER_PURE_ONCE_ASM_REWRITE_RULE f thl th =
    PURE_ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th
fun FILTER_ONCE_ASM_REWRITE_RULE f thl th =
    ONCE_REWRITE_RULE ((map ASSUME (filter f (hyp th))) @ thl) th;;
fun FILTER_PURE_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (fn asl => PURE_REWRITE_TAC ((filter (f o concl) asl)@thl))
fun FILTER_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (fn asl => REWRITE_TAC ((filter (f o concl) asl) @ thl))
fun FILTER_PURE_ONCE_ASM_REWRITE_TAC f L =
    ASSUM_LIST (fn l => PURE_ONCE_REWRITE_TAC ((filter (f o concl) l) @ L))
fun FILTER_ONCE_ASM_REWRITE_TAC f thl =
    ASSUM_LIST (fn asl => ONCE_REWRITE_TAC ((filter (f o concl) asl) @ thl));


fun GEN_REWRITE_CONV rw_func thl =
   rw_func (REWRITES_CONV (add_rewrites empty_rewrites thl));

fun GEN_REWRITE_RULE rw_func thl =
    CONV_RULE (GEN_REWRITE_CONV rw_func thl);

fun GEN_REWRITE_TAC rw_func thl =
    CONV_TAC (GEN_REWRITE_CONV rw_func thl);


(***************************************************************************
 * SUBST_MATCH (|-u=v) th   searches for an instance of u in
 * (the conclusion of) th and then substitutes the corresponding
 * instance of v. Much faster than rewriting.
 ****************************************************************************)

local fun find_match u =
       let val hom = ho_match_term [] empty_tmset u
           fun find_mt t =
               hom t handle HOL_ERR _ =>
               find_mt(rator t)  handle HOL_ERR _ =>
               find_mt(rand t)   handle HOL_ERR _ =>
               find_mt(body t)   handle HOL_ERR _ =>
               raise ERR "SUBST_MATCH" "no match"
       in find_mt
       end
in
fun SUBST_MATCH eqth th =
 SUBS [Drule.INST_TY_TERM (find_match(lhs(concl eqth)) (concl th)) eqth] th
end;


(* -------------------------------------------------------------------------
 * Useful instance of more general higher order matching.
 * Taken directly from the GTT source code (Don Syme).
 *
 * val LOCAL_COND_ELIM_THM1 = prove
 *     ((--`!P:'a->bool. P(a => b | c) = (~a \/ P(b)) /\ (a \/ P(c))`--),
 *      GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[]);
 *
 * val conv = HIGHER_REWRITE_CONV[LOCAL_COND_ELIM_THM1];
 * val x = conv (--`(P:'a -> bool) (a => b | c)`--);
 * val x = conv (--`(a + (f x => 0 | n) + m) = 0`--) handle e => Raise e;
 * ------------------------------------------------------------------------- *)


val HIGHER_REWRITE_CONV =
  let fun GINST th =
      let val fvs = HOLset.listItems
                       (HOLset.difference(FVL[concl th]empty_tmset,
                                          hyp_frees th))
          val gvs = map (genvar o type_of) fvs
      in INST (map2 (curry op |->) fvs gvs) th
      end
  in fn ths =>
      let val thl = map (GINST o SPEC_ALL) ths
          val concs = map concl thl
          val lefts = map lhs concs
          val (preds,pats) = unzip(map dest_comb lefts)
          val beta_fns = map2 BETA_VAR preds concs
          val ass_list = zip pats (zip preds (zip thl beta_fns))
          fun insert p = Ho_Net.enter ([],p,p)
          val mnet = itlist insert pats Ho_Net.empty
          fun look_fn t = mapfilter
                    (fn p => if can (ho_match_term [] empty_tmset p) t then p
                             else fail())
                    (lookup t mnet)
      in fn tm =>
          let val ts = find_terms
                        (fn t => not (null (look_fn t)) andalso free_in t tm) tm
              val stm = Lib.trye hd (sort free_in ts)
              val pat = Lib.trye hd (look_fn stm)
              val (tmin,tyin) = ho_match_term [] empty_tmset pat stm
              val (pred,(th,beta_fn)) = op_assoc aconv pat ass_list
              val gv = genvar(type_of stm)
              val abs = mk_abs(gv,subst[stm |-> gv] tm)
              val (tmin0,tyin0) = ho_match_term [] empty_tmset pred abs
          in CONV_RULE beta_fn (INST tmin (INST tmin0 (INST_TYPE tyin0 th)))
          end
      end
      handle e => raise (wrap_exn "Ho_Rewrite" "HIGHER_REWRITE_CONV" e)
  end;

end (* Ho_Rewrite *)
