(* ========================================================================= *)
(* A HOL INTERFACE TO THE FIRST-ORDER PROVERS.                               *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

(*
loadPath := ["../basic", "../fol", "../metis", "../normalize"] @ !loadPath;
app load
["mlibUseful", "mlibSolver", "normalForms", "normalFormsTheory", "folMapping"];
*)

(*
*)
structure folTools :> folTools =
struct

open HolKernel Parse boolLib combinTheory simpLib
     normalFormsTheory normalForms folMapping;

infix THEN ORELSE THENC ##;

type 'a pp       = 'a mlibUseful.pp;
type 'a stream   = 'a mlibStream.stream;
type term1       = mlibTerm.term;
type formula1    = mlibTerm.formula;
type thm1        = mlibThm.thm;
type limit       = mlibMeter.limit
type solver_node = mlibSolver.solver_node;
type vars        = term list * hol_type list;

(* ------------------------------------------------------------------------- *)
(* Chatting.                                                                 *)
(* ------------------------------------------------------------------------- *)

val () = mlibUseful.traces := insert "folTools" (!mlibUseful.traces);

val chat = mlibUseful.trace "folTools";

(* ------------------------------------------------------------------------- *)
(* Mapping parameters.                                                       *)
(* ------------------------------------------------------------------------- *)

type Mparm = folMapping.parameters;

type parameters =
  {equality   : bool,              (* Add equality axioms if needed *)
   combinator : bool,              (* Add combinator reduction rules *)
   boolean    : bool,              (* Add rules for reasoning about booleans *)
   mapping    : Mparm};

val defaults =
  {equality   = true,
   combinator = false,
   boolean    = false,
   mapping    = folMapping.defaults};

fun update_parm_equality f (parm : parameters) : parameters =
  let
    val {equality, boolean, combinator, mapping} = parm
  in
    {equality = f equality, boolean = boolean, combinator = combinator,
     mapping = mapping}
  end;

fun update_parm_boolean f (parm : parameters) : parameters =
  let
    val {equality, boolean, combinator, mapping} = parm
  in
    {equality = equality, boolean = f boolean, combinator = combinator,
     mapping = mapping}
  end;

fun update_parm_combinator f (parm : parameters) : parameters =
  let
    val {equality, boolean, combinator, mapping} = parm
  in
    {equality = equality, boolean = boolean, combinator = f combinator,
     mapping = mapping}
  end;

fun update_parm_mapping f (parm : parameters) : parameters =
  let
    val {equality, boolean, combinator, mapping} = parm
  in
    {equality = equality, boolean = boolean, combinator = combinator,
     mapping = f mapping}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val ERR = mk_HOL_ERR "folTools";
val BUG = mlibUseful.BUG;

fun possibly f x = case total f x of SOME y => y | NONE => x;

fun timed_fn s f a =
  let
    val (t, r) = mlibUseful.timed f a
    val () = chat (s ^ mlibUseful.real_to_string t ^ "\n")
  in
    r
  end;

fun map_tl f =
  let
    open mlibStream
    fun mtl NIL = NIL
      | mtl (CONS (h, t)) = CONS (h, f (mtl' t))
    and mtl' s () = mtl (s ())
  in
    f o mtl'
  end;

val type_vars_in_terms = foldl (fn (h, t) => union (type_vars_in_term h) t) [];

fun strip_dom_rng 0 ty = ([], ty)
  | strip_dom_rng n ty =
  let val (d, r) = dom_rng ty in (cons d ## I) (strip_dom_rng (n - 1) r) end;

fun const_scheme c =
  let val {Thy, Name, ...} = dest_thy_const c
  in prim_mk_const {Name = Name, Thy = Thy}
  end;

fun mk_vthm th =
  let
    val tm = concl th
    val tyV = subtract (type_vars_in_term tm) (type_vars_in_terms (hyp th))
    val (tmV, _) = strip_forall tm
    val gtmV = map (genvar o type_of) tmV
  in
    ((gtmV, tyV), SPECL gtmV th)
  end;

fun list_mk_conj' [] = T
  | list_mk_conj' tms = list_mk_conj tms;

fun strip_disj' tm = if tm = F then [] else strip_disj tm;

fun CONJUNCTS' th = if concl th = T then [] else CONJUNCTS th;

val thm_atoms = map (possibly dest_neg) o strip_disj' o concl;

val varnames = matchTools.vfree_names is_var o list_mk_conj';

(* ------------------------------------------------------------------------- *)
(* If recent_fol_problems is set to NONE then nothing happens (the default). *)
(* If it is set to SOME l then every compiled FOL problem is cons'ed to l.   *)
(* ------------------------------------------------------------------------- *)

type fol_problem = {thms : thm1 list, hyps : thm1 list, query : formula1 list};

val recent_fol_problems : fol_problem list option ref = ref NONE;

fun save_fol_problem (t, h, q) =
  case !recent_fol_problems of NONE => ()
  | SOME l
    => recent_fol_problems := SOME ({thms = t, hyps = h, query = q} :: l);

(* ------------------------------------------------------------------------- *)
(* Logic maps manage the interface between HOL and first-order logic.        *)
(* ------------------------------------------------------------------------- *)

type logic_map =
  {parm   : parameters,
   axioms : (thm1 * (vars * thm)) list,
   thms   : thm1 list,
   hyps   : thm1 list,
   consts : string list};

fun new_map parm : logic_map =
  {parm = parm, axioms = [], thms = [], hyps = [], consts = []};

val empty_map = new_map defaults;

fun add_thm vth lmap : logic_map =
  let
    val {parm, axioms, thms, hyps, consts} = lmap
    val th = hol_thm_to_fol (#mapping parm) vth
  in
    if mem th thms then lmap
    else
      {parm = parm, axioms = (th, vth) :: axioms, thms = th :: thms,
       hyps = hyps, consts = consts}
  end;

fun add_hyp vth lmap : logic_map =
  let
    val {parm, axioms, thms, hyps, consts} = lmap
    val th = hol_thm_to_fol (#mapping parm) vth
  in
    if mem th hyps then lmap
    else
      {parm = parm, axioms = (th, vth) :: axioms, thms = thms,
       hyps = th :: hyps, consts = consts}
  end;

fun add_const s {parm, axioms, thms, hyps, consts} : logic_map =
  {parm = parm, axioms = axioms, thms = thms, hyps = hyps,
   consts = insert s consts};

val add_thms = C (foldl (uncurry add_thm));

val pp_logic_map : logic_map pp =
  mlibUseful.pp_map (fn {hyps, thms, ...} => (rev hyps, rev thms))
  (mlibUseful.pp_pair (mlibUseful.pp_list pp_thm1) (mlibUseful.pp_list pp_thm1));

(* ------------------------------------------------------------------------- *)
(* Equality axioms.                                                          *)
(* ------------------------------------------------------------------------- *)

val EQ_SYMTRANS = prove
  (``!x y z. ~(x:'a = y) \/ ~(x = z) \/ (y = z)``,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC ``x:'a = y`` THEN
   ASM_REWRITE_TAC
   [ONCE_REWRITE_RULE [boolTheory.DISJ_SYM]
    (REWRITE_RULE[] boolTheory.BOOL_CASES_AX)]);

val EQ_COMB = prove
  (``!f g x y. ~(f:'a->'b = g) \/ ~(x = y) \/ (f x = g y)``,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC ``x:'a = y`` THEN
   ASM_CASES_TAC ``f:'a->'b = g`` THEN
   ASM_REWRITE_TAC []);

val EQ_BOOL = prove
  (``!x y. ~x \/ ~(x = y) \/ y``,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC ``x:bool`` THEN
   ASM_CASES_TAC ``y:bool`` THEN
   ASM_REWRITE_TAC []);

local
  fun break tm (res, subs) =
    let
      val (f, args) = strip_comb tm
      val f_n = (if is_const f then const_scheme f else f, length args)
    in
      (insert f_n res, args @ subs)
    end;

  fun boolify (tm, len) =
    let val (_, ty) = strip_dom_rng len (type_of tm)
    in (if ty = bool then tm else inst [ty |-> bool] tm, len)
    end;

  val raw_relations = (map boolify ## I) o foldl (uncurry break) ([], []);

  fun harvest (res, []) = res
    | harvest (res, tm :: others) = harvest (break tm (res, others));

  fun plumb (r, s) = {rels = r, funs = harvest ([], s)};
in
  val rels_in_atoms    = fst o raw_relations;
  val relfuns_in_atoms = plumb o raw_relations;
end;

local
  val imp_elim_CONV = REWR_CONV (tautLib.TAUT `(a ==> b) = ~a \/ b`);
  val eq_elim_RULE = MATCH_MP (tautLib.TAUT `(a = b) ==> b \/ ~a`);
  fun paired_C f (x, y) = f (y, x);

  fun mk_axiom pflag (tm, len) =
    let
      val (ctys, rty) = strip_dom_rng len (type_of tm)
      val largs = map genvar ctys
      val rargs = map genvar ctys
      val th1 = foldl (paired_C MK_COMB) (REFL tm)
        (map (ASSUME o mk_eq) (zip largs rargs))
      val th2 = if pflag then try eq_elim_RULE th1 else th1
      val th3 =
        foldr (fn (e, th) => CONV_RULE imp_elim_CONV (DISCH e th)) th2 (hyp th2)
    in
      GENL (largs @ rargs) th3
    end;

  fun mk_axioms pflag = map (mk_axiom pflag) o filter (fn (_, x) => 0 < x);
in
  fun substitution_thms skols {rels, funs} =
    let
      fun is_skol v = is_var v andalso mem (fst (dest_var v)) skols
      val funs = filter (not o is_skol o fst) funs
    in
      map mk_vthm (mk_axioms true rels @ mk_axioms false funs)
    end;
end;

local
  val eq_tm      = ``$= :'a->'a->bool``;
  val eq_thms    = map mk_vthm [EQ_REFL, EQ_SYMTRANS];
  val eq_thms_ho = map mk_vthm [EQ_COMB, EQ_BOOL] @ eq_thms;
in
  fun add_equality_axioms (lmap as {parm, axioms, consts, ...}) : logic_map =
    if not (#equality parm) then lmap else
      C add_thms lmap
      let
        val atoms = flatten (map (thm_atoms o snd o snd) axioms)
      in
        if not (exists (equal eq_tm o fst) (rels_in_atoms atoms)) then []
        else if #higher_order (#mapping parm) then eq_thms_ho
        else eq_thms @ substitution_thms consts (relfuns_in_atoms atoms)
      end
    handle HOL_ERR _ => raise BUG "add_equality_axioms" "shouldn't fail";
end;

(* ------------------------------------------------------------------------- *)
(* Combinator reduction theorems.                                            *)
(* ------------------------------------------------------------------------- *)

val EXT_POINT = CONV_RULE CNF_CONV EXT_POINT_DEF;

local
  val comb_thms = map mk_vthm [S_THM, K_THM, I_THM, C_THM, o_THM, EXT_POINT];
in
  fun add_combinator_thms lmap : logic_map =
    let
      val {parm as {combinator, mapping, ...}, ...} = lmap
    in
      if not combinator orelse not (#higher_order mapping) then lmap
      else add_thms comb_thms lmap
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Boolean theorems.                                                         *)
(* ------------------------------------------------------------------------- *)

val FALSITY'     = prove (``~F``, REWRITE_TAC []);

val NOT_CLAUSES' = (map GEN_ALL o CONJUNCTS o SPEC_ALL) NOT_CLAUSES;
val IMP_CLAUSES' = (map GEN_ALL o CONJUNCTS o SPEC_ALL) IMP_CLAUSES;
val OR_CLAUSES'  = (map GEN_ALL o CONJUNCTS o SPEC_ALL) OR_CLAUSES;
val AND_CLAUSES' = (map GEN_ALL o CONJUNCTS o SPEC_ALL) AND_CLAUSES;
val EQ_CLAUSES'  = (map GEN_ALL o CONJUNCTS o SPEC_ALL) EQ_CLAUSES;

val EXCLUDED_MIDDLE' = prove
  (``!t. (t = T) \/ (t = F)``,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC ``t:bool`` THEN
   ASM_REWRITE_TAC []);

(* Could use these instead: needs experiments with a decent first-order *)
(* to decide which is best.
val IMPLICATION =
  let
    val tm = Term `p = (A ==> B)`
  in
    map (GENL [``A:bool``, ``B:bool``])
    (CONJUNCTS
     (MP
      (SPEC ``A ==> B``
       (GEN ``p:bool``
        (DISCH tm
         (CONV_RULE CNF_CONV
          (REWRITE_RULE [SYM (ASSUME tm)] (SPEC_ALL IMP_DISJ_THM))))))
        (REFL ``A ==> B``)))
  end;

val NEGATION = prove
  (``!a. ~a = (a ==> F)``,
   REWRITE_TAC [IMP_CLAUSES]);

val DISJUNCTION = prove
  (``!a b. (a \/ b) = (~a ==> b)``,
   REWRITE_TAC [IMP_DISJ_THM]);

val CONJUNCTION = prove
  (``!a b. (a /\ b) = ~(a ==> ~b)``,
   REWRITE_TAC [IMP_DISJ_THM, DE_MORGAN_THM]);
*)

val UNIVERSALITY = prove
  (``!(p : 'a -> bool). $! p = (p = K T)``,
   GEN_TAC THEN
   (SUFF_TAC ``(!x : 'a. p x) = (p = K T)`` THEN1
    (CONV_TAC (DEPTH_CONV ETA_CONV) THEN
     DISCH_THEN ACCEPT_TAC)) THEN
   EQ_TAC THENL
   [DISCH_TAC THEN
    MATCH_MP_TAC EQ_EXT THEN
    GEN_TAC THEN
    REWRITE_TAC [K_THM] THEN
    POP_ASSUM MATCH_ACCEPT_TAC,
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [K_THM]]);

val FORALL_TRUE = prove
  (``$! (K T : 'a -> bool)``,
   REWRITE_TAC [UNIVERSALITY]);

val FORALL_FALSE = prove
  (``~$! (K F : 'a -> bool)``,
   REWRITE_TAC [UNIVERSALITY] THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   REWRITE_TAC [K_THM]);

val EXISTENTIALITY = prove
  (``!(p : 'a -> bool). $? p = ~(p = K F)``,
   GEN_TAC THEN
   (KNOW_TAC ``(p : 'a -> bool) = (\x. p x)`` THEN1
    (CONV_TAC (DEPTH_CONV ETA_CONV) THEN
     REFL_TAC)) THEN
   DISCH_THEN SUBST1_TAC THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   REWRITE_TAC [K_THM] THEN
   BETA_TAC THEN
   CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) THEN
   REWRITE_TAC []);

val EXISTS_TRUE = prove
  (``$? (K T : 'a -> bool)``,
   REWRITE_TAC [EXISTENTIALITY] THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   REWRITE_TAC [K_THM]);

val EXISTS_FALSE = prove
  (``~$? (K F : 'a -> bool)``,
   REWRITE_TAC [EXISTENTIALITY]);

local
  val simple_bool_thms =
    map mk_vthm
    [TRUTH, FALSITY', FORALL_TRUE, FORALL_FALSE, EXISTS_TRUE, EXISTS_FALSE];

  val gen_bool_thms =
    simple_bool_thms @
    map mk_vthm
    (EXCLUDED_MIDDLE' :: UNIVERSALITY :: EXISTENTIALITY ::
     NOT_CLAUSES' @ IMP_CLAUSES' @ OR_CLAUSES' @ AND_CLAUSES' @ EQ_CLAUSES');
in
  fun add_boolean_thms lmap : logic_map =
    let
      val {parm as {boolean, mapping, ...}, ...} = lmap
    in
      if not (#higher_order mapping) then lmap
      else add_thms (if boolean then gen_bool_thms else simple_bool_thms) lmap
    end;
end;

(* ------------------------------------------------------------------------- *)
(* A pure interface to the first-order prover: zero normalization.           *)
(* ------------------------------------------------------------------------- *)

type Query  = vars * term list;
type Result = vars * thm list;

fun initialize_solver solv init =
  mlibStream.partial_map I o
  ((mlibSolver.solved_filter o mlibSolver.subsumed_filter)
   (mlibSolver.initialize solv init));

fun eliminate consts =
  mlibStream.filter
  (fn (_, ths) =>
   null (intersect consts (varnames (map concl ths))) orelse
   (chat "folTools: solution contained a skolem const: dropping.\n"; false));

fun FOL_SOLVER solv lmap lim =
  let
    val {parm, axioms, thms, hyps, consts} =
      (add_equality_axioms o add_boolean_thms o add_combinator_thms) lmap
    val (thms, hyps) = (rev thms, rev hyps)
    val solver =
      timed_fn "folTools: solver initialization time: "
      (initialize_solver solv) {thms = thms, hyps = hyps, limit = lim}
    fun exn_handler f x = f x
      handle Time => raise ERR "FOL_SOLVER" "Time exception raised"
  in
    fn query =>
    let
      val q =
        if snd query = [F] then [mlibTerm.False]
        else hol_literals_to_fol (#mapping parm) query
      val () = save_fol_problem (thms, hyps, q)
      val lift = fol_thms_to_hol (#mapping parm) (C assoc axioms) query
      val timed_lift = timed_fn "folTools: proof translation time: " lift
      val timed_stream =
        map_tl (timed_fn "folTools: proof search time: " o exn_handler)
    in
      eliminate consts
      (mlibStream.map timed_lift (timed_stream (fn () => solver q) ()))
    end
  end;

(* ------------------------------------------------------------------------- *)
(* HOL normalization to first-order form.                                    *)
(* ------------------------------------------------------------------------- *)

val FOL_NORM_CONV =
  REDEPTH_CONV BETA_CONV    THENC
  DELAMB_CONV               THENC
  SIMP_CONV cond_lift_ss [] THENC
  CNF_CONV;

val FOL_NORM_RULE = CONV_RULE FOL_NORM_CONV;

(* ------------------------------------------------------------------------- *)
(* A basic interface to the first-order prover.                              *)
(* ------------------------------------------------------------------------- *)

type Init = {parm : parameters, thms : thm list, hyps : thm list, lim : limit};

local
  fun iconst (cs, th) =
    let val c = NEW_SKOLEM_CONST th
    in (fst (strip_comb c) :: cs, SKOLEM_CONST_RULE c th)
    end;

  fun ithm th =
    let
      val th = FOL_NORM_RULE th
      val (h, c) = (hyp th, concl th)
      val tyV = subtract (type_vars_in_term c) (type_vars_in_terms h)
      val (cs, th) = curry (repeat iconst) [] th
      val vths = map (mk_vthm o GEN_ALL) (CONJUNCTS' th)
    in
      (map (fst o dest_var) cs, map ((I ## K tyV) ## I) vths)
    end;

  fun append2 (a, b) (c, d) = (a @ c, b @ d);

  fun init ({parm, thms, hyps, ...} : Init) =
    let
      val (cs, thms) = foldl (uncurry (C append2 o ithm)) ([], []) thms
      val (cs, hyps) = foldl (uncurry (C append2 o ithm)) (cs, []) hyps
      val lmap = new_map parm
      val lmap = foldl (fn (t, m) => possibly (add_thm t) m) lmap thms
      val lmap = foldl (fn (t, m) => possibly (add_hyp t) m) lmap hyps
      val lmap = foldl (fn (c, m) => add_const c m) lmap cs
    in
      lmap
    end
    handle HOL_ERR _ => raise BUG "init_map" "shouldn't fail";
in
  val init_map = timed_fn "folTools: normalization time: " init
end;

local
  fun end_find s =
    mlibStream.hd s handle Empty => raise ERR "FOL_FIND" "no solution found";

  fun end_refute (_, [t]) = CLEANUP_SKOLEM_CONSTS_RULE t
    | end_refute _ = raise BUG "FOL_REFUTE" "weird";
in
  fun FOL_SOLVE slv (init as {lim, ...}) = FOL_SOLVER slv (init_map init) lim;
  fun FOL_FIND slv init = end_find o FOL_SOLVE slv init;
  fun FOL_REFUTE slv init = (end_refute o FOL_FIND slv init) (([], []), [F]);
end;

(* ------------------------------------------------------------------------- *)
(* Stripping, elimination of choice operator (@), then FOL_NORM_CONV.        *)
(* ------------------------------------------------------------------------- *)

fun NEW_CHOOSE_THEN ttac th =
  (X_CHOOSE_THEN o genvar o type_of o bvar o rand o concl) th ttac th;

val FOL_STRIP_THM_THEN = FIRST_TCL [CONJUNCTS_THEN, NEW_CHOOSE_THEN];

val FOL_STRIP_ASSUME_TAC = REPEAT_TCL FOL_STRIP_THM_THEN CHECK_ASSUME_TAC;

val FOL_STRIP_TAC =
  EQ_TAC ORELSE
  GEN_TAC ORELSE
  CONJ_TAC ORELSE
  DISCH_THEN FOL_STRIP_ASSUME_TAC;

val FOL_NORM_TAC =
  timed_fn "folTools: tactic normalization time: "
  (REPEAT FOL_STRIP_TAC THEN
   CCONTR_TAC THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   SELECT_TAC THEN
   CONV_TAC (REPEATC (REWR_CONV AND_IMP_INTRO)) THEN

   (* Strictly speaking, this next line is logically unnecessary, but tends *)
   (* to give a big speed-up to normalization and proof translation phases. *)
   (* Check out GILMORE_9 for an example of this phenomenon. *)
   CONV_TAC (RATOR_CONV (RAND_CONV FOL_NORM_CONV)) THEN

   FOL_STRIP_TAC);

(* ------------------------------------------------------------------------- *)
(* Calling the first-order prover from a HOL tactic.                         *)
(* ------------------------------------------------------------------------- *)

fun FOL_TAC (slv, parm, lim) ths =
  let fun init asms = {parm = parm, thms = ths, hyps = asms, lim = lim}
  in FOL_NORM_TAC THEN ASSUM_LIST (ACCEPT_TAC o FOL_REFUTE slv o init)
  end;

end