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
(* Chatting and error handling.                                              *)
(* ------------------------------------------------------------------------- *)

local
  open mlibUseful;
  val module = "folTools";
in
  val () = traces := {module = module, alignment = I} :: !traces;
  fun chatting l = tracing {module = module, level = l};
  fun chat s = (trace s; true)
  val ERR = mk_HOL_ERR module;
  val BUG = BUG;
end;

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

fun update_equality f (parm : parameters) : parameters =
  let
    val {equality, boolean, combinator, mapping} = parm
  in
    {equality = f equality, boolean = boolean, combinator = combinator,
     mapping = mapping}
  end;

fun update_boolean f (parm : parameters) : parameters =
  let
    val {equality, boolean, combinator, mapping} = parm
  in
    {equality = equality, boolean = f boolean, combinator = combinator,
     mapping = mapping}
  end;

fun update_combinator f (parm : parameters) : parameters =
  let
    val {equality, boolean, combinator, mapping} = parm
  in
    {equality = equality, boolean = boolean, combinator = f combinator,
     mapping = mapping}
  end;

fun update_mapping f (parm : parameters) : parameters =
  let
    val {equality, boolean, combinator, mapping} = parm
  in
    {equality = equality, boolean = boolean, combinator = combinator,
     mapping = f mapping}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun possibly f x = f x handle HOL_ERR _ => x;

fun timed_fn s f a =
  let
    val (t, r) = mlibUseful.timed f a
    val _ = chatting 1 andalso chat
      ("metis: " ^ s ^ " time: " ^ mlibUseful.real_to_string t ^ "\n")
  in
    r
  end;

val type_vars_in_terms = foldl (fn (h, t) => union (type_vars_in_term h) t) [];

fun variant_tys avoid =
  let
    fun f acc _ 0 = acc
      | f acc i n =
      let val v = mk_vartype ("'ty" ^ int_to_string i)
      in if mem v avoid then f acc (i + 1) n else f (v :: acc) (i + 1) (n - 1)
      end
  in
    f [] 0
  end;

fun strip_dom_rng ty =
  case total dom_rng ty of NONE => ([], ty)
  | SOME (d, r) => (cons d ## I) (strip_dom_rng r);

fun strip_dom_rng_n 0 ty = ([], ty)
  | strip_dom_rng_n n ty =
  let val (d, r) = dom_rng ty in (cons d ## I) (strip_dom_rng_n (n - 1) r) end;

fun const_scheme c =
  let val {Thy, Name, ...} = dest_thy_const c
  in prim_mk_const {Name = Name, Thy = Thy}
  end;

fun const_scheme_n n f =
  let
    val c = const_scheme f
    val (ds, r) = strip_dom_rng (type_of c)
    val diff = n - length ds
  in
    if diff <= 0 then c else
      let
        val _ = is_vartype r orelse raise ERR "const_scheme_n" "inflexible"
        val xs = variant_tys (type_varsl (r :: ds)) diff
      in
        inst [r |-> foldl op--> r xs] c
      end
  end;

fun mk_vthm_ty tyV th =
  let
    val (tmV, _) = strip_forall (concl th)
    val gtmV = map (genvar o type_of) tmV
  in
    ((gtmV, tyV), SPECL gtmV th)
  end;

fun mk_vthm th =
  let
    val tyV_c = type_vars_in_term (concl th)
    val tyV_h = type_vars_in_terms (hyp th)
  in
    mk_vthm_ty (subtract tyV_c tyV_h) th
  end;

fun list_mk_conj' [] = T
  | list_mk_conj' tms = list_mk_conj tms;

fun strip_disj' tm = if tm = F then [] else strip_disj tm;

fun CONJUNCTS' th = if concl th = T then [] else CONJUNCTS th;

fun GSPEC' th =
  let
    val (vs,_) = strip_forall (concl th)
    val gvs = map (genvar o type_of) vs
  in
    (gvs, SPECL gvs th)
  end;

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
    val _ = chatting 3 andalso
            chat ("adding thm:\n" ^ thm_to_string (snd vth) ^ "\n")
    val {parm, axioms, thms, hyps, consts} = lmap
    val th = hol_thm_to_fol (#mapping parm) vth
  in
    {parm = parm, axioms = (th, vth) :: axioms,
     thms = mlibThm.FRESH_VARS th :: thms, hyps = hyps, consts = consts}
  end;

fun add_hyp vth lmap : logic_map =
  let
    val _ = chatting 3 andalso
            chat ("adding hyp:\n" ^ thm_to_string (snd vth) ^ "\n")
    val {parm, axioms, thms, hyps, consts} = lmap
    val th = hol_thm_to_fol (#mapping parm) vth
  in
    {parm = parm, axioms = (th, vth) :: axioms, thms = thms,
     hyps = mlibThm.FRESH_VARS th :: hyps, consts = consts}
  end;

fun add_const s {parm, axioms, thms, hyps, consts} : logic_map =
  {parm = parm, axioms = axioms, thms = thms, hyps = hyps,
   consts = insert s consts};

val add_thms = C (foldl (uncurry add_thm));

local
  fun is_def cs tm =
    case total (fst o dest_var o lhs) tm of NONE => false | SOME c => mem c cs;

  fun iconst (cs,th) =
    let val c = (genvar o type_of o fst o dest_exists o concl) th
    in (fst (dest_var c) :: cs, SKOLEM_CONST_RULE c th)
    end;

  fun ithm (th,(cs,vths)) =
    let
      val h = List.filter (not o is_def cs) (hyp th)
      val tyV = subtract (type_vars_in_term (concl th)) (type_vars_in_terms h)
      val (cs,th) = repeat iconst (cs,th)
      val (tmV,th) = GSPEC' th
      val vths' = map (pair (tmV,tyV)) (CONJUNCTS' th)
    in
      (cs, vths @ vths')
    end;

  fun carefully s f t m = f t m
    handle HOL_ERR _ =>
      (chatting 1 andalso chat
       ("metis: raised exception adding " ^ s ^ ": dropping.\n"); m);
in
  fun build_map (parm,cs,thmhyps) =
    let
      val _ = chatting 3 andalso chat "metis: beginning build_map.\n"
      val (thms, hyps) = partition (null o hyp) thmhyps
      val _ = chatting 3 andalso chat "metis: partitioned thms and hyps.\n"
      val (cs,thms) = foldl ithm (cs,[]) thms
      val _ = chatting 3 andalso chat "metis: applied ithm to theorems.\n"
      val (cs,hyps) = foldl ithm (cs,[]) hyps
      val _ = chatting 3 andalso chat "metis: applied ithm to hypotheses.\n"
      val lmap = new_map parm
      val lmap = foldl (fn(t,m)=>carefully"a theorem"add_thm t m) lmap thms
      val lmap = foldl (fn(t,m)=>carefully"an assumption"add_hyp t m) lmap hyps
      val lmap = foldl (fn(c,m)=>add_const c m) lmap cs
    in
      lmap
    end
    handle HOL_ERR _ => raise BUG "build_map" "shouldn't fail";
end;

val pp_logic_map : logic_map pp =
  mlibUseful.pp_map (fn {hyps, thms, ...} => (rev hyps, rev thms))
  (mlibUseful.pp_pair (mlibUseful.pp_list mlibThm.pp_thm) (mlibUseful.pp_list mlibThm.pp_thm));

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

val EQ_EXTENSION =
  CONV_RULE CNF_CONV EXT_POINT_DEF ::
  (map GEN_ALL o CONJUNCTS o SPEC_ALL o CONV_RULE CNF_CONV o
   INST_TYPE [beta |-> bool]) EXT_POINT_DEF;

local
  fun break tm (res, subtms) =
    let
      val (f, args) = strip_comb tm
      val n = length args
      val f = if is_const f then const_scheme_n n f else f
    in
      (insert (f, n) res, args @ subtms)
    end;

  fun boolify (tm, len) =
    let val (_, ty) = strip_dom_rng_n len (type_of tm)
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
      val (ctys, rty) = strip_dom_rng_n len (type_of tm)
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
      fun is_eql (t,2) = same_const equality t | is_eql _ = false
      val funs = filter (not o is_skol o fst) funs
      val rels = filter (not o is_eql) rels
    in
      map mk_vthm (mk_axioms true rels @ mk_axioms false funs)
    end;
end;

local
  val eq_tm      = ``$= :'a->'a->bool``;
  val eq_thms    = map mk_vthm [EQ_REFL, EQ_SYMTRANS];
  val eq_thms_ho = map mk_vthm (EQ_COMB :: EQ_BOOL :: EQ_EXTENSION) @ eq_thms;
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

local
  val fo_thms = map mk_vthm [K_THM, I_THM];
  val ho_thms = fo_thms @ map mk_vthm [S_THM, C_THM, o_THM];
in
  fun add_combinator_thms lmap : logic_map =
    let
      val {parm as {combinator, mapping, ...}, ...} = lmap
    in
      if not combinator then lmap
      else add_thms (if #higher_order mapping then ho_thms else fo_thms) lmap
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
      C add_thms lmap
      (if not (#higher_order mapping) then []
       else if boolean then gen_bool_thms else simple_bool_thms)
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
   (chatting 1 andalso
    chat "metis: solution contained a skolem const: dropping.\n";
    chatting 2 andalso
    chat (foldl (fn (h,t) => t ^ "  " ^ thm_to_string h ^ "\n") "" ths);
    false));

fun FOL_SOLVE solv lmap lim =
  let
    val {parm, axioms, thms, hyps, consts} =
      (add_equality_axioms o add_boolean_thms o add_combinator_thms) lmap
    val (thms, hyps) = (rev thms, rev hyps)
    val solver =
      timed_fn "solver initialization"
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
      val timed_lift = timed_fn "proof translation" lift
      val timed_stream = mlibStream.map_thk (timed_fn "proof search" o exn_handler)
    in
      eliminate consts
      (mlibStream.map timed_lift (timed_stream (fn () => solver q) ()))
    end
  end;

local
  fun end_find s =
    mlibStream.hd s handle Empty => raise ERR "FOL_FIND" "no solution found";
in
  fun FOL_FIND slv lmap lim = end_find o FOL_SOLVE slv lmap lim;
end;

local
  fun end_refute (_, [t]) = CLEANUP_SKOLEM_CONSTS_RULE t
    | end_refute _ = raise BUG "FOL_REFUTE" "weird";
in
  fun FOL_REFUTE slv lmap lim =
    (end_refute o FOL_FIND slv lmap lim) (([], []), [F]);
end;

fun FOL_TACTIC slv lmap lim = ACCEPT_TAC (FOL_REFUTE slv lmap lim);

(* ------------------------------------------------------------------------- *)
(* HOL normalization to first-order form.                                    *)
(* ------------------------------------------------------------------------- *)

val FOL_NORM = (map (fst o dest_var) ## I) o MIN_CNF;

(* Normalization tactic = Stripping + Elimination of @ *)

fun NEW_CHOOSE_THEN ttac th =
  (X_CHOOSE_THEN o genvar o type_of o bvar o rand o concl) th ttac th;

val FOL_STRIP_THM_THEN =
  FIRST_TCL [CONJUNCTS_THEN, NEW_CHOOSE_THEN, DISJ_CASES_THEN];

val FOL_STRIP_ASSUME_TAC = REPEAT_TCL FOL_STRIP_THM_THEN CHECK_ASSUME_TAC;

val NEW_GEN_TAC = W (X_GEN_TAC o genvar o type_of o fst o dest_forall o snd);

val FOL_STRIP_TAC =
  EQ_TAC
  ORELSE NEW_GEN_TAC
  ORELSE CONJ_TAC
  ORELSE DISCH_THEN FOL_STRIP_ASSUME_TAC;

val FOL_NORM_TAC =
  (REPEAT FOL_STRIP_TAC
   THEN CCONTR_TAC
   THEN REPEAT (POP_ASSUM MP_TAC)
   THEN SELECT_TAC
   THEN REPEAT FOL_STRIP_TAC);

(* A flexible tactic that performs normalization of theorems and goal. *)

fun FOL_NORM_TTAC tac ths =
  let
    fun f asms = FOL_NORM (asms @ ths)
  in
    timed_fn "tactic normalization" FOL_NORM_TAC
    THEN POP_ASSUM_LIST (tac o timed_fn "theorem normalization" f)
  end;

end
