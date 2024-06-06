structure subtypeTools :> subtypeTools =
struct

open HolKernel Parse boolLib BasicProvers;

open Susp combinTheory pred_setTheory hurdUtils subtypeTheory ho_discrimTools
     ho_proverTools ho_basicTools;

infixr 0 oo ## THENC ORELSEC THENR ORELSER -->;
infix 1 |->;
infix thenf orelsef then_frule orelse_frule join_frule;

val assert = simple_assert;

(* ------------------------------------------------------------------------- *)
(* Debugging.                                                                *)
(* ------------------------------------------------------------------------- *)

val trace_level = ref 0;
val _ = Feedback.register_trace ("subtypeTools", trace_level, 10);
fun trace l s = if l > !trace_level then () else say (s ^ "\n");
fun trace_x l s f x =
  if l > !trace_level then () else say (s ^ ":\n" ^ f x ^ "\n");
fun trace_CONV l s tm = (trace_x l s term_to_string tm; ALL_CONV tm);

(* ------------------------------------------------------------------------- *)
(* Term operations                                                           *)
(* ------------------------------------------------------------------------- *)

fun genvar_dest_foralls tm =
  let
    val (vars, body) = dest_foralls tm
    val (gvars, (sub, _)) = term_new_vars vars
  in
    (gvars, subst sub body)
  end;

fun mk_in (v, set) =
  let
    val v_type = type_of v
    val in_type = v_type --> (v_type --> bool) --> bool
    val in_const = mk_const ("IN", in_type)
  in
    list_mk_comb (in_const, [v, set])
  end;
val dest_in = dest_binop "IN";
val is_in = can dest_in;

fun mk_subset (set1, set2) =
  let
    val set_type = type_of set1
    val subset_type = set_type --> set_type --> bool
    val subset_const = mk_const ("SUBSET", subset_type)
  in
    list_mk_comb (subset_const, [set1, set2])
  end;
val dest_subset = dest_binop "SUBSET";
val is_subset = can dest_subset;

(* ------------------------------------------------------------------------- *)
(* vterms                                                                    *)
(* ------------------------------------------------------------------------- *)

fun term_to_vterm tm =
  let
    val vars = (free_vars tm, type_vars_in_term tm)
    val (vars', (sub, _)) = new_vars vars
  in
    (vars', pinst sub tm)
  end;

(* ========================================================================= *)
(* Some general functions operating on congruences.                          *)
(* ========================================================================= *)

local
  fun imp_conv tm = (if is_imp tm then ALL_CONV else REWR_CONV EQ_T_IMP) tm

  fun conj_conv tm =
    (if Teq tm then ALL_CONV else FORALLS_CONV imp_conv) tm

  val canon_conv =
    FORALLS_CONV
    (imp_conv THENC
     RATOR_CONV
     (RAND_CONV (EXACT_CONV T ORELSEC CONJUNCT_CONV (FORALLS_CONV imp_conv))))
in
  val cong_canon = CONV_RULE canon_conv
end;

fun find_matching_cong congs tm =
  let
    val ((sub, thk), (vars, th)) =
      case ovdiscrim_ho_match congs tm of c :: _ => c
      | [] => raise ERR "find_matching_cong" "no applicable congruence"
    val vars' = vars_after_subst vars sub
    val conv = RAND_CONV (RATOR_CONV (RAND_CONV (K (SYM (thk ())))))
    val (vars'', (sub', _)) = new_vars vars'
    val th' = (PINST sub THENR CONV_RULE conv THENR PINST sub') th
  in
    (vars'', th')
  end;

(* Function cacheing *)
type 'a ccache = (term * int, 'a) Binarymap.dict ref

fun new_cache () : 'a ccache =
    ref (Binarymap.mkDict (pair_compare(Term.compare, Int.compare)))

fun cache_lookup c (a, b_thk) =
    case Binarymap.peek(!c, a) of
      SOME b => b
    | NONE => let
        val b = b_thk ()
        val _ = c := Binarymap.insert(!c,a,b)
      in
        b
      end

fun cachef f =
  let
    val c = new_cache ()
  in
    fn a => cache_lookup c (a, fn () => f a)
  end;

(* ========================================================================= *)
(* Predicate subtype-checking.                                               *)
(* ========================================================================= *)

(* Types *)

datatype psubtype_context = PSUBTYPE_CONTEXT of
  {facts : factdb, subtypes : vthm ovdiscrim};

datatype subtype_context = SUBTYPE_CONTEXT of
  {pure : psubtype_context susp,
   ccache : vthm list ccache};

datatype subtype_context_element =
  SC_SUBTYPE of thm
  | SC_SIMPLIFICATION of thm
  | SC_JUDGEMENT of thm;

(* Tuning *)

val cache_subtypes = ref true;
val subtype_depth = ref 3;

(* (Quite delicate :-) interface to the higher-order prover *)

val set_cnf_frule : fact_rule =
  first_frule
  [neg_frule, true_frule, false_frule, disj_frule, conj_frule,
   forall_frule, exists_frule, (*bool_lrule,*) equal_frule, merge_frule];

val set_factdb =
  (factdb_add_norm set_cnf_frule o
   factdb_add_norm basic_rewrite_frule)
  null_factdb;

fun set_meson_frule db : fact_rule =
  joinl_frule [biresolution_frule db, equality_frule, k1_frule];

fun set_prove_depth db depth vgoal =
  meson_prove_reduce_depth db (set_meson_frule db) depth vgoal;

(* Basic operations *)

val empty_psubtype_context =
  PSUBTYPE_CONTEXT {facts = set_factdb, subtypes = empty_ovdiscrim};

fun dest_psubtype_context (PSUBTYPE_CONTEXT sc) = sc;
val psubtype_context_facts = #facts o dest_psubtype_context;
val psubtype_context_subtypes = #subtypes o dest_psubtype_context;
fun psubtype_context_update_facts f (PSUBTYPE_CONTEXT {facts, subtypes}) =
  PSUBTYPE_CONTEXT {facts = f facts, subtypes = subtypes};
fun psubtype_context_update_subtypes f (PSUBTYPE_CONTEXT {facts, subtypes}) =
  PSUBTYPE_CONTEXT {facts = facts, subtypes = f subtypes};

fun new_subtype_context () =
  SUBTYPE_CONTEXT
  {pure = delay (K empty_psubtype_context),
   ccache = new_cache ()};

fun dest_subtype_context (SUBTYPE_CONTEXT sc) = sc;
val subtype_context_pure = force o #pure o dest_subtype_context;
val subtype_context_ccache = #ccache o dest_subtype_context;
val subtype_context_facts = psubtype_context_facts o subtype_context_pure;
val subtype_context_subtypes = psubtype_context_subtypes o subtype_context_pure;
fun subtype_context_update_facts f (SUBTYPE_CONTEXT {pure, ccache}) =
  SUBTYPE_CONTEXT
  {pure = delay (fn () => psubtype_context_update_facts f (force pure)),
   ccache = ccache};
fun subtype_context_update_subtypes f (SUBTYPE_CONTEXT {pure, ccache}) =
  SUBTYPE_CONTEXT
  {pure = delay (fn () => psubtype_context_update_subtypes f (force pure)),
   ccache = ccache};

fun subtype_context_initialize sc = (subtype_context_pure sc; sc);

(* Pretty-printing *)
open PP
fun pp_psubtype_context (PSUBTYPE_CONTEXT c) =
    block CONSISTENT 1 [
      block CONSISTENT 2 [
        add_string "{#facts =",
        add_break (1, 0),
        pp_int (factdb_size (#facts c)),
        add_string ","
      ],
      add_break (1, 0),
      block CONSISTENT 2 [
        add_string "#subtypes =",
        add_break (1, 0),
        pp_int (ovdiscrim_size (#subtypes c)),
        add_string "}"
      ]
    ]

val pp_subtype_context = pp_map subtype_context_pure pp_psubtype_context;

(* Adding to psubtype_contexts *)

fun add_subtype_vthm (vars, th) =
  let
    val tm = (fst o dest_in o snd o dest_imp o concl) th
  in
    ovdiscrim_add ((vars, tm), (vars, th))
  end;

val add_subtype_thm = add_subtype_vthm o thm_to_vthm o cong_canon;

fun add_simplification th = factdb_add_norm (rewrite_frule [thm_to_vthm th]);

fun subtype_context_add_fact vth =
  subtype_context_update_facts (factdb_add_vthm vth);

fun subtype_context_add_judgement th =
  subtype_context_add_fact (thm_to_vthm (TRYR (MATCH_MP EQ_SUBSET_SUBSET) th));

val subtype_context_add_judgements = C (trans subtype_context_add_judgement);

fun subtype_context_add (SC_SUBTYPE th) =
  subtype_context_update_subtypes (add_subtype_thm th)
  | subtype_context_add (SC_SIMPLIFICATION th) =
  subtype_context_update_facts (add_simplification th)
  | subtype_context_add (SC_JUDGEMENT th) = subtype_context_add_judgement th;

(* The type-checking engine *)

type cond_prover = vars * substitution -> ((vars * substitution) * thm) list;

local
  fun conj res [] = res
    | conj res ((vs, ts, []) :: others) =
    conj ((vs, REV_CONJUNCTS ts) :: res) others
    | conj res (((vars, sub), ts, p :: ps) :: others) =
    let
      val vts = p (vars, sub)
      fun f ((vars', sub'), t) =
        ((vars', refine_subst sub sub'), t :: map (PINST sub') ts, ps)
    in
      conj res (map f vts @ others)
    end;
in
  fun conj_provers [] = raise BUG "string_provers" "no provers to string"
    | conj_provers (ps : cond_prover list) : cond_prover =
    fn vs => conj [] [(vs, [], ps)]
end;

fun k_prover th : cond_prover = fn vars_sub => [(vars_sub, th)];

fun dest_trivial cond =
  let
    val (bvars, (asm, heart)) = ((I ## dest_imp) o dest_foralls) cond
    val (elt, set) = dest_in heart
    val _ = assert (fst (dest_const set) = "UNIV")
  in
    (bvars, asm, elt)
  end;
val is_trivial = can dest_trivial;

fun prove_trivial cond =
  let
    val (bvars, asm, elt) = dest_trivial cond
  in
    GENL (rev bvars) (DISCH asm (ISPEC elt IN_UNIV))
  end;

fun subtype_check ccache congs stricttypechecking depth =
  let
    fun cached_basic_subtypes facts tm =
      if not (!cache_subtypes) orelse not (null (free_vars tm)) then
        basic_subtypes facts tm
      else
        cache_lookup ccache
        ((tm, depth), fn () => basic_subtypes facts tm)
    and basic_subtypes facts tm =
      let
        val _ = trace_x 4 "basic_subtypes: tm" term_to_string tm
        val (vars, th) = find_matching_cong congs tm
        val conds = (conjuncts o fst o dest_imp o concl) th
        val _ =
          trace_x 4 "basic_subtypes: conds"
          (list_to_string term_to_string) conds
        val cond_provers = map (cond_prover facts) conds
        val cond_results = conj_provers cond_provers (vars, empty_subst)
        val _ =
          assert (not stricttypechecking orelse not (null cond_results))
          (ERR "subtypecheck"
           ("no basic type for subterm:\n" ^ term_to_string tm))
        fun process_result ((vars', sub'), th') = (vars', MP (PINST sub' th) th')
      in
        partial_map (total process_result) cond_results
      end
    and cond_prover facts cond =
      if Teq cond then k_prover TRUTH
      else if not stricttypechecking andalso is_trivial cond then
        k_prover (prove_trivial cond)
      else
        let
          val (bvars, body) = genvar_dest_foralls cond
          val (asm, elt_set) = dest_imp body
          val (elt, set) = dest_in elt_set
          val elt_th = QCONV (N_BETA_CONV (length bvars)) elt
          val elt' = RHS elt_th
          val facts' = factdb_add_vthm (empty_vars, ASSUME asm) facts
          val basics = cached_basic_subtypes facts' elt'
          val facts'' = factdb_add_vthms basics facts'
          val canon_rule =
            CONV_RULE (RATOR_CONV (RAND_CONV (K (SYM elt_th)))) THENR
            DISCH asm THENR
            GENL (rev bvars)
          fun canon_result (s, (v, th)) = ((v, s), canon_rule th)
        in
          fn (before_vars, before_sub) =>
          let
            val set' = pinst before_sub set
            val goal = mk_in (elt', set')
            val pre_results = set_prove_depth facts'' depth (before_vars, goal)
            val results = map canon_result pre_results
          in
            results
          end
        end
  in
    cached_basic_subtypes
  end;

fun SUBTYPE_CHECK stricttypechecking depth sc tm =
  subtype_check (subtype_context_ccache sc) (subtype_context_subtypes sc)
  stricttypechecking depth (subtype_context_facts sc) tm;

(* Type skeletons are perhaps useful for free variables       *)
(* (or maybe are best left in the closet...)                  *)
(* Example:                                                   *)
(* Input: ('a -> 'b) -> 'c                                    *)
(* Output: !v : ('a -> 'b) -> 'c. v IN (UNIV -> UNIV) -> UNIV *)

local
  val UNIV = ``UNIV : 'a -> bool``

  fun set ty = ty --> bool
in
  fun mk_skeleton_eq ty =
    if can dom_rng ty then
      let
        val (dom, rng) = dom_rng ty
        val (dom_eq, rng_eq) = Df mk_skeleton_eq (dom, rng)
        val c = mk_const ("FUNSET", set dom --> set rng --> set ty)
        val set_eq = MK_COMB (MK_COMB (REFL c, dom_eq), rng_eq)
      in
        TRANS set_eq (INST_TY [alpha |-> dom, beta |-> rng] UNIV_FUNSET_UNIV)
      end
    else REFL (inst_ty [alpha |-> ty] UNIV)

  val mk_skeleton = MATCH_MP IN_EQ_UNIV_IMP o mk_skeleton_eq
end;

(* HOL conversions and tactics *)

fun SUBTYPE_MATCH depth sc (vars, goal) =
  let
    val (elt, _) = dest_in goal
    val subtypes = SUBTYPE_CHECK false depth sc elt
    val facts = factdb_add_vthms subtypes (subtype_context_facts sc)
    val res = set_prove_depth facts depth (vars, goal)
  in
    res
  end;

fun SUBTYPE_PROVE depth sc goal =
  (case SUBTYPE_MATCH depth sc (empty_vars, goal) of (_, (_, th)) :: _ => th
   | [] => raise ERR "SUBTYPE_PROVE" "couldn't!")

fun SUBTYPE_CONV_DEPTH depth sc goal = EQT_INTRO (SUBTYPE_PROVE depth sc goal);

val SUBTYPE_CONV = SUBTYPE_CONV_DEPTH (!subtype_depth);

fun SUBTYPE_TAC sc : tactic =
  ASSUM_LIST
  (fn ths =>
   CONV_TAC (SUBTYPE_CONV (subtype_context_add_judgements ths sc)));

(* ========================================================================= *)
(* A simplifier skeleton using predicate subtyping as a decision procedure.  *)
(* ========================================================================= *)

(* Types *)

type c_rule = ho_substitution -> vthm -> vthm list;
type c_rewr = ho_substitution -> conv -> (term -> thm) -> conv;

datatype context = CONTEXT of
  {subtypes : subtype_context,
   forwards : thm list,
   rules : c_rule ovdiscrim,
   congs : vthm ovdiscrim,
   rewrs : c_rewr ovdiscrim};

datatype context_element =
  C_THM of thm
  | C_REWR of vterm * c_rewr
  | C_CONG of thm
  | C_RULE of vterm * c_rule
  | C_SUBTYPE of subtype_context_element
  | C_FORWARDS of thm;

(* Tuning parameters *)

val simplify_max_traversals = ref 5;
val simplify_max_depth = ref 3;
val simplify_max_rewrites = ref 10;
val simplify_subtype_depth = ref 3;
val simplify_forwards = ref 10;

(* Pretty-printing *)

fun pp_context (CONTEXT c) =
    block INCONSISTENT 1 [
      block CONSISTENT 2 [
        add_string "{subtypes =",
        add_break (1, 0),
        pp_subtype_context (#subtypes c),
        add_string ","
      ],
      add_break (1, 0),

      block CONSISTENT 2 [
        add_string "#forwards =",
        add_break (1, 0),
        pp_int (length (#forwards c)),
        add_string ","
      ],
      add_break (1, 0),

      block CONSISTENT 2 [
        add_string "#congs =",
        add_break (1, 0),
        pp_int (ovdiscrim_size (#congs c)),
        add_string ","
      ],
      add_break (1, 0),

      block CONSISTENT 2 [
        add_string "#rules =",
        add_break (1, 0),
        pp_int (ovdiscrim_size (#rules c)),
        add_string ","
      ],
      add_break (1, 0),

      block CONSISTENT 2 [
        add_string "#rewrs =",
        add_break (1, 0),
        pp_int (ovdiscrim_size (#rewrs c)),
        add_string "}"
      ]
    ]

(* Basic context operations *)

fun new_context () = CONTEXT
  {subtypes = new_subtype_context (),
   forwards = [],
   rules = empty_ovdiscrim,
   congs = empty_ovdiscrim,
   rewrs = empty_ovdiscrim};

fun dest_context (CONTEXT c) = c;
val context_subtypes = #subtypes o dest_context;
val context_forwards = #forwards o dest_context;
val context_rules = #rules o dest_context;
val context_congs = #congs o dest_context;
val context_rewrs = #rewrs o dest_context;

fun context_update_subtypes f
  (CONTEXT {subtypes, forwards, rules, congs, rewrs}) =
  CONTEXT {subtypes = f subtypes, forwards = forwards, rules = rules,
           congs = congs, rewrs = rewrs};

fun context_update_forwards f
  (CONTEXT {subtypes, forwards, rules, congs, rewrs}) =
  CONTEXT {subtypes = subtypes, forwards = f forwards, rules = rules,
           congs = congs, rewrs = rewrs};

fun context_update_rules f
  (CONTEXT {subtypes, forwards, rules, congs, rewrs}) =
  CONTEXT {subtypes = subtypes, forwards = forwards, rules = f rules,
           congs = congs, rewrs = rewrs};

fun context_update_congs f
  (CONTEXT {subtypes, forwards, rules, congs, rewrs}) =
  CONTEXT {subtypes = subtypes, forwards = forwards, rules = rules,
           congs = f congs, rewrs = rewrs};

fun context_update_rewrs f
  (CONTEXT {subtypes, forwards, rules, congs, rewrs}) =
  CONTEXT {subtypes = subtypes, forwards = forwards, rules = rules,
           congs = congs, rewrs = f rewrs};

fun rewr_vthm_to_rewr (vars : vars, th) : vterm * c_rewr =
  let
    val (cond, (pat, _)) = ((I ## dest_eq) o dest_imp o concl) th
    val f = ho_subst_COND_REWR th o (if Teq cond then K (K TRUTH) else I)
    fun rewr ho_sub _ prover (_ : term) = f prover ho_sub
  in
    ((vars, pat), rewr)
  end;

local
  val undisch_asm = ((fst o dest_imp o concl) ## UNDISCH) o D

  fun imp_rule (asms, (vars, th)) =
    let
      val (asm, th') = undisch_asm th
    in
      (asm :: asms, (vars, th'))
    end

  fun is_subterm tm1 tm2 = can (find_term (aconv tm1)) tm2

  fun good_rewr (vars, _) th =
    let
      val _ = trace_x 2 "vthm_to_rewr_vthms: th" thm_to_string th
      val (asm, (l, r)) = ((I ## dest_eq) o dest_imp o concl) th
      val res =
        not (is_subterm l asm) andalso not (is_subterm l r) andalso
        (HOLset.isSubset (listset vars Isct FVLset [asm, r], FVs l))
      val _ = trace 2
        ("vthm_to_rewr_vthms: " ^ (if res then "accepted" else "rejected"))
    in
      res
    end;
in
  fun vthm_to_rewr_vthms rules =
    let
      fun break res [] = res
        | break res ((asms, (vars, th)) :: rest) =
        let
          val tm = concl th
          val matches = ovdiscrim_ho_match rules tm
        in
          case partial_first (fn (s, f) => total (f s) (vars, th)) matches of
            SOME split => break res (map (add_fst asms) split @ rest)
            | NONE =>
            if is_imp tm then
              break res (imp_rule (asms, (vars, th)) :: rest)
            else
              let
                val rewr_thm =
                  ((if is_eq (concl th) then ALL_RULE else EQT_INTRO) THENR
                   CONV_RULE (REPEATC EQ_NEG_BOOL_CONV) THENR
                   (if null asms then DISCH T else DISCH_CONJUNCTS asms)) th
                val res' =
                  (if good_rewr vars rewr_thm then cons (vars, rewr_thm)
                   else I) res
              in
                break res' rest
              end
        end
    in
      fn vthm => break [] [([], vthm)]
    end;
end;

fun thm_to_rewr_vthms rules = vthm_to_rewr_vthms rules o thm_to_vthm;

fun vthm_to_rewrs rules = map rewr_vthm_to_rewr o vthm_to_rewr_vthms rules;
fun thm_to_rewrs rules = vthm_to_rewrs rules o thm_to_vthm;

fun pattern_thing (tm, r) =
  (term_to_vterm tm, fn (_ : ho_substitution) => r);

fun pattern_rewr x : vterm * c_rewr = pattern_thing x;

fun pattern_rule x : vterm * c_rule = pattern_thing x;

(* Adding things to contexts *)

val context_add_subtype = context_update_subtypes o subtype_context_add;
val context_add_forwards = context_update_forwards o cons;
val context_add_rewr = context_update_rewrs o ovdiscrim_add;
val context_add_rewrs = C (trans context_add_rewr);
val context_add_rule = context_update_rules o ovdiscrim_add;

local
  fun prepare (vars, th) =
    let
      val tm = (fst o dest_eq o snd o dest_imp o concl) th
    in
      ((vars, tm), (vars, th))
    end;

  val prepare_cong = prepare o thm_to_vthm o cong_canon;
in
  val context_add_cong = context_update_congs o ovdiscrim_add o prepare_cong
end;

fun context_add_fact x ctext =
  (context_update_subtypes (subtype_context_add_fact x) o
   context_add_rewrs (vthm_to_rewrs (context_rules ctext) x)) ctext;

val context_add_facts = C (trans context_add_fact);

fun context_add_thm x ctext =
  context_add_rewrs (thm_to_rewrs (context_rules ctext) x) ctext;

val context_add_thms = C (trans context_add_thm);

fun context_add_element (C_THM th) = context_add_thm th
  | context_add_element (C_FORWARDS th) = context_add_forwards th
  | context_add_element (C_REWR r) = context_add_rewr r
  | context_add_element (C_CONG c) = context_add_cong c
  | context_add_element (C_RULE r) = context_add_rule r
  | context_add_element (C_SUBTYPE s) = context_add_subtype s;

val context_add_elements = C (trans context_add_element);

(* The core rewriting engine *)

local
  local
    fun align vars' vars opat tm =
      let
        val (bvar, body) = dest_abs tm
        val _ = assert (is_genvar bvar) (ERR "alpha_align" "not a genvar abs")
        val (v, sub_opat) =
          if (case opat of SOME pat => is_abs pat | NONE => false) then
            (I ## SOME) (dest_abs (grab opat))
          else (mk_var ("v", type_of bvar), NONE)
        val v' = variant (all_vars body @ vars') v
      in
        mk_abs (v', align (v' :: vars') (bvar :: vars) sub_opat body)
      end
    handle (HOL_ERR _) => subst (zipwith (curry op|->) vars vars') tm
  in
    fun alpha_align pat tm =
      let
        val res = align [] [] (SOME pat) tm
      in
        res
      end
  end;

  fun match_align bvars l r tm =
    let
      val n = length bvars
      val tm_abs = trans (curry mk_abs) tm bvars
      val l_body = N n rator l
      val tm_pretty_abs = alpha_align l_body tm_abs
      val tm' = fold (C (curry mk_comb)) tm_pretty_abs bvars
      val tm_th = QCONV (N n (fn c => RATOR_CONV c THENC BETA_CONV) ALL_CONV) tm'
      val (r_var, r_bvs) = list_dest_comb r
      val _ = assert (tml_eq bvars (rev r_bvs)) (BUG "match_align" "bvar panic")
      val res = (([r_var |-> tm_pretty_abs], []), SYM tm_th)
    in
      res
    end
    handle (h as HOL_ERR _) => raise err_BUG "match_align" h;

  fun eval_rewr rewr ctext cond =
    let
      val (bvars, body) = genvar_dest_foralls cond
      val (asm, (l, r)) = ((I ## dest_eq) o dest_imp) body
      val ctext' =
        if Teq asm  then ctext
        else context_add_fact (empty_vars, ASSUME asm) ctext
      val raw_eq = QCONV (N_BETA_CONV (length bvars) THENC rewr ctext') l
      val (sub, match_eq) = match_align bvars l r (RHS raw_eq)
      val res_eq = (DISCH asm THENR GENL (rev bvars)) (TRANS raw_eq match_eq)
    in
      (sub, res_eq)
    end
    handle (h as HOL_ERR _) => raise err_BUG "eval_rewr" h;

  fun eval_rewrs _ _ res [] = res
    | eval_rewrs rewr ctext (sub, CONDS) (cond :: rest) =
    let
      val (sub', COND) = eval_rewr rewr ctext (pinst sub cond)
    in
      eval_rewrs rewr ctext (refine_subst sub sub', COND :: CONDS) rest
    end
    handle (h as HOL_ERR _) => raise err_BUG "eval_rewrs" h;

  fun execute_cong rewr ctext (vars, th) =
    let
      val conds = (conjuncts o fst o dest_imp o concl) th
      val (sub, CONDS) = eval_rewrs rewr ctext (empty_subst, []) conds
      val res = MP (PINST sub th) (REV_CONJUNCTS CONDS)
    in
      res
    end
    handle (h as HOL_ERR _) => raise err_BUG "execute_cong" h;
in
  fun SIMPLIFY_CONG_CONV rewr ctext tm =
    let
      val cong = find_matching_cong (context_congs ctext) tm
      val res = execute_cong rewr ctext cong
    in
      res
    end
end;

fun SIMPLIFY_REWR_CONV simper prover rewrs tm =
  let
    val _ = trace_x 4 "SIMPLIFY_REWR_CONV: input" term_to_string tm
    val matches = ovdiscrim_ho_match rewrs tm
    val _ =
      trace_x 4 "SIMPLIFY_REWR_CONV: #matches" (int_to_string o length) matches
    val conv = FIRSTC (map (fn (ho_sub, f) => f ho_sub simper prover) matches)
  in
    (QCONV conv THENC
     trace_CONV 4 "SIMPLIFY_REWR_CONV result") tm
  end;

(* Warning: do not eta-reduce this function! *)
fun GEN_SIMPLIFY_CONV s p ctext tm =
  QCONV
  ((TRYC o REPEATC_CUTOFF (!simplify_max_traversals) o CHANGED_CONV)
   (trace_CONV 2 "GEN_SIMPLIFY_CONV input" THENC
    TRYC (REPEATC_CUTOFF (!simplify_max_rewrites)
          (SIMPLIFY_REWR_CONV (GEN_SIMPLIFY_CONV s p ctext)
           (s ctext) (context_rewrs ctext))) THENC
    trace_CONV 2 "GEN_SIMPLIFY_CONV after rewr" THENC
    TRYC (p ctext) THENC
    TRYC (SIMPLIFY_CONG_CONV (GEN_SIMPLIFY_CONV s p) ctext) THENC
    trace_CONV 2 "GEN_SIMPLIFY_CONV result")) tm;

val no_prover_conv : context -> conv = K NO_CONV;

fun subtype_prover_conv ctext =
  QCONV (SUBTYPE_CONV_DEPTH (!simplify_subtype_depth) (context_subtypes ctext));

(* Warning: do not eta-reduce this function! *)
fun SIMPLIFY_CONV_DEPTH 0 _ _ = raise ERR "SIMPLIFY_CONV" "too deep!"
  | SIMPLIFY_CONV_DEPTH n ctext tm =
  QCONV
  (GEN_SIMPLIFY_CONV (EQT_ELIM oo SIMPLIFY_CONV_DEPTH (n - 1))
   subtype_prover_conv ctext) tm;

fun SIMPLIFY_CONV' ctext tm =
  QCONV (SIMPLIFY_CONV_DEPTH (!simplify_max_depth) ctext) tm;

fun SIMPLIFY_CONV ctext =
  QCONV
  (trace_CONV 1 "SIMPLIFY_CONV input" THENC
   GEN_SIMPLIFY_CONV (EQT_ELIM oo SIMPLIFY_CONV') no_prover_conv ctext THENC
   TRYC (subtype_prover_conv ctext) THENC
   trace_CONV 1 "SIMPLIFY_CONV result");

fun SIMPLIFY_TAC_X conv ctext ths =
  let
    val ths' = map GEN_ALL ths
  in
    ASSUM_LIST
    (CONV_TAC o
     conv o
     C context_add_facts ctext o
     map thm_to_vthm o
     MATCH_MP_DEPTH (!simplify_forwards) (ths' @ context_forwards ctext) o
     append ths')
  end;

fun PRESIMPLIFY_TAC ctext ths =
    EVERY (map (ASSUME_TAC o GEN_ALL) ths)
 >> ASM_MATCH_MP_TAC (ths @ context_forwards ctext);

val SIMPLIFY_TAC' = SIMPLIFY_TAC_X SIMPLIFY_CONV';
val SIMPLIFY_TAC = SIMPLIFY_TAC_X SIMPLIFY_CONV;

fun ASM_SIMPLIFY_TAC_X tac ctext ths = POP_ASSUM_TAC (tac ctext ths);
val ASM_SIMPLIFY_TAC' = ASM_SIMPLIFY_TAC_X SIMPLIFY_TAC';
val ASM_SIMPLIFY_TAC = ASM_SIMPLIFY_TAC_X SIMPLIFY_TAC;

fun SIMPLIFY_TACS ctext =
  (SIMPLIFY_TAC ctext, ASM_SIMPLIFY_TAC ctext,
   SIMPLIFY_TAC' ctext, ASM_SIMPLIFY_TAC' ctext);

(* ------------------------------------------------------------------------- *)
(* Simplification modules.                                                   *)
(* ------------------------------------------------------------------------- *)

datatype precontext = PRECONTEXT of (string * context_element list) list;

val empty_precontext = PRECONTEXT [];

val pp_precontext = pp_map (fn PRECONTEXT pc => map fst pc) (pp_list pp_string);

fun precontext_add (n, f) (PRECONTEXT p) =
  (assert (not (exists (curry op= n o fst) p))
   (ERR "precontext_add" (n ^ " already exists in precontext"));
   PRECONTEXT (p @ [(n, f)]));

fun precontext_compile (PRECONTEXT p) =
  (context_update_subtypes subtype_context_initialize o
   context_add_elements (flatten (map snd p))) (new_context ());

fun precontext_merge (PRECONTEXT p1) (PRECONTEXT p2) =
  PRECONTEXT (p1 @ filter (fn (n, _) => not (exists (equal n o fst) p1)) p2);

fun precontext_mergel [] = empty_precontext
  | precontext_mergel (p::rest) = precontext_merge p (precontext_mergel rest);

(* ------------------------------------------------------------------------- *)
(* Subtype-checking examples.                                                *)
(* ------------------------------------------------------------------------- *)

(*
set_trace "subtypeTools" 3;

val stc = tt4 SUBTYPE_CHECK true 3 (context_subtypes hol_c);

stc ``!f :: UNIV -> UNIV. f x``;
stc ``!f :: UNIV -> UNIV -> UNIV. f x x``;
stc ``\x. x``;
stc ``\x. [x]``;
stc ``!x :: nzreal. x / x = 1``;
stc ``\x y :: nzreal. MAP inv [x; y]``;
stc ``\x :: negreal. FUNPOW inv n x``;
stc ``\x :: posreal. sqrt (FUNPOW inv n x)``;
stc ``MAP inv (~1 :: MAP sqrt [1; 1])``;
stc ``!x :: P. x IN P /\ x IN Q``;

stc ``~3 : real``;

ff stc ``inv x * x = 1``;
stc ``x IN nzreal ==> (inv x * x = 1)``;
stc ``inv IN (real -> nzreal) ==> (inv x * x = 1)``;
stc ``inv IN (real -> real) ==> (inv x * x = 1)``;
*)

(* ------------------------------------------------------------------------- *)
(* Subtype-checking plus rewriting examples.                                 *)
(* ------------------------------------------------------------------------- *)

(*
allow_trace "execute_cong";
allow_trace "eval_rewr";
allow_trace "match_align";
allow_trace "alpha_align";
allow_trace "SIMPLIFY_TYPECHECK";
allow_trace "SIMPLIFY_TYPECHECK: (tm, res)";
allow_trace "SUBTYPE_MATCH";
allow_trace "GEN_SIMPLIFY_CONV input";
allow_trace "GEN_SIMPLIFY_CONV result";
reset_traces ();
allow_trace "SIMPLIFY_CONV";

tt prove
(``~3 IN nzreal``,
 SUBTYPE_TAC (context_subtypes hol_c));

tt prove
(``(MAP inv (CONS (~1) (MAP sqrt [3; 1]))) IN list nzreal``,
 SUBTYPE_TAC (context_subtypes hol_c));

tt prove
(``(\x :: negreal. FUNPOW inv n x) IN negreal -> negreal``,
 SUBTYPE_TAC (context_subtypes hol_c));

tt prove
(``(!x :: nzreal. x / x = 1) ==> (5 / 5 = 3 / 3)``,
 SIMPLIFY_TAC hol_c []);
*)


(* non-interactive mode
*)
end;
