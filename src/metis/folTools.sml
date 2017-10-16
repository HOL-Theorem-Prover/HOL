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

structure Parse = struct
  open Parse
  val (Type,Term) = parse_from_grammars normalFormsTheory.normalForms_grammars
end
open Parse

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
  fun BUG f m = Bug (f ^ ": " ^ m);
end;

(* ------------------------------------------------------------------------- *)
(* Mapping parameters.                                                       *)
(* ------------------------------------------------------------------------- *)

type parameters =
  {equality : bool, combinator : bool, boolean : bool,
   mapping_parm : folMapping.parameters};

type 'a parmupdate = ('a -> 'a) -> parameters -> parameters;

val defaults =
  {equality = false, combinator = false, boolean = false,
   mapping_parm = folMapping.defaults};

fun update_equality f (parm : parameters) : parameters =
  let
    val {equality,combinator,boolean,mapping_parm} = parm
  in
    {equality = f equality, combinator = combinator, boolean = boolean,
     mapping_parm = mapping_parm}
  end;

fun update_combinator f (parm : parameters) : parameters =
  let
    val {equality,combinator,boolean,mapping_parm} = parm
  in
    {equality = equality, combinator = f combinator, boolean = boolean,
     mapping_parm = mapping_parm}
  end;

fun update_boolean f (parm : parameters) : parameters =
  let
    val {equality,combinator,boolean,mapping_parm} = parm
  in
    {equality = equality, combinator = combinator, boolean = f boolean,
     mapping_parm = mapping_parm}
  end;

fun update_mapping_parm f (parm : parameters) : parameters =
  let
    val {equality,combinator,boolean,mapping_parm} = parm
  in
    {equality = equality, combinator = combinator, boolean = boolean,
     mapping_parm = f mapping_parm}
  end;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun possibly f x = f x handle HOL_ERR _ => x;

fun timed_fn s f a =
  let
    val (t,r) = mlibUseful.timed f a
    val _ = chatting 2 andalso chat
      ("metis: " ^ s ^ " time: " ^ mlibUseful.real_to_string t ^ "\n")
  in
    r
  end;

fun map_thk f =
    let
      fun m mlibStream.NIL = mlibStream.NIL
        | m (mlibStream.CONS (h,t)) = mlibStream.CONS (h, m' t)
      and m' t () = m (f t ())
    in
      m'
    end;

val type_vars_in_terms = foldl (fn (h,t) => union (type_vars_in_term h) t) [];

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

fun strip_disj' tm = if aconv tm F then [] else strip_disj tm;

fun CONJUNCTS' th = if aconv (concl th) T then [] else CONJUNCTS th;

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
    val _ = chatting 5 andalso
            chat ("adding thm:\n" ^ thm_to_string (snd vth) ^ "\n")
    val {parm, axioms, thms, hyps, consts} = lmap
    val th = hol_thm_to_fol (#mapping_parm parm) vth
  in
    {parm = parm, axioms = (th, vth) :: axioms,
     thms = mlibThm.FRESH_VARS th :: thms, hyps = hyps, consts = consts}
  end;

fun add_hyp vth lmap : logic_map =
  let
    val _ = chatting 5 andalso
            chat ("adding hyp:\n" ^ thm_to_string (snd vth) ^ "\n")
    val {parm, axioms, thms, hyps, consts} = lmap
    val th = hol_thm_to_fol (#mapping_parm parm) vth
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
      (chatting 2 andalso chat
       ("metis: raised exception adding " ^ s ^ ": dropping.\n"); m);
in
  fun build_map (parm,cs,thmhyps) =
    let
      val _ = chatting 5 andalso chat "metis: beginning build_map.\n"
      val (thms, hyps) = partition (null o hyp) thmhyps
      val _ = chatting 5 andalso chat "metis: partitioned thms and hyps.\n"
      val (cs,thms) = foldl ithm (cs,[]) thms
      val _ = chatting 5 andalso chat "metis: applied ithm to theorems.\n"
      val (cs,hyps) = foldl ithm (cs,[]) hyps
      val _ = chatting 5 andalso chat "metis: applied ithm to hypotheses.\n"
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

val EQ_EXTENSION = CONV_RULE CNF_CONV EXT_POINT_DEF;

local
  fun tmi_eq (tm1,i1) (tm2,i2:int) = aconv tm1 tm2 andalso i1 = i2

  fun break tm (res, subtms) =
    let
      val (f, args) = strip_comb tm
      val n = length args
      val f = if is_const f then const_scheme_n n f else f
    in
      (op_insert tmi_eq (f, n) res, args @ subtms)
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
  val eq_tm = ``$= :'a->'a->bool``;
  val neq_fo = [mk_vthm EQ_REFL]
  and xeq_fo = [mk_vthm EQ_SYMTRANS];
  val eq_fo = neq_fo @ xeq_fo;

  val neq_ho = neq_fo @ [mk_vthm EQ_EXTENSION]
  and xeq_ho = xeq_fo @ map mk_vthm [EQ_COMB];
  val eq_ho = neq_ho @ xeq_ho;
in
  fun add_equality_thms (lmap : logic_map) =
    C add_thms lmap
    let
      val {parm,axioms,consts,...} = lmap
      val {equality,mapping_parm,...} = parm
      val {higher_order,...} = mapping_parm
    in
      if not equality then if higher_order then neq_ho else neq_fo
      else
        let
          val atoms = flatten (map (thm_atoms o snd o snd) axioms)
        in
          if not (exists (aconv eq_tm o fst) (rels_in_atoms atoms)) then []
          else if higher_order then eq_ho
          else eq_fo @ substitution_thms consts (relfuns_in_atoms atoms)
        end
    end
    handle HOL_ERR _ => raise BUG "add_equality_thms" "shouldn't fail";
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
      val {parm as {combinator, mapping_parm, ...}, ...} = lmap
      val {higher_order,...} = mapping_parm
    in
      if not combinator then lmap
      else add_thms (if higher_order then ho_thms else fo_thms) lmap
    end;
end;

(* ------------------------------------------------------------------------- *)
(* Boolean theorems.                                                         *)
(* ------------------------------------------------------------------------- *)

val FALSITY' = prove (``~F``, REWRITE_TAC []);

val EQ_BOOL = (CONJUNCTS o prove)
  (``(!x y. ~x \/ ~(x = y) \/ y) /\
     (!x y. x \/ (x = y) \/ y) /\
     (!x y. ~x \/ (x = y) \/ ~y)``,
   REPEAT CONJ_TAC THEN
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC ``x:bool`` THEN
   ASM_CASES_TAC ``y:bool`` THEN
   ASM_REWRITE_TAC []);

local
  val simple_bool = map mk_vthm [TRUTH, FALSITY'];
  val gen_bool = simple_bool @ map mk_vthm EQ_BOOL;
in
  fun add_boolean_thms lmap : logic_map =
    C add_thms lmap
    let
      val {parm,...} = lmap
      val {boolean,mapping_parm,...} = parm
      val {higher_order,...} = mapping_parm
    in
      if not higher_order then []
      else if boolean then gen_bool else simple_bool
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
   (chatting 2 andalso
    chat "metis: solution contained a skolem const: dropping.\n";
    chatting 4 andalso
    chat (foldl (fn (h,t) => t ^ "  " ^ thm_to_string h ^ "\n") "" ths);
    false));

fun FOL_SOLVE solv lmap lim =
  let
    val {parm, axioms, thms, hyps, consts} =
      (add_equality_thms o add_boolean_thms o add_combinator_thms) lmap
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
        if ListPair.allEq (uncurry aconv) (snd query, [F]) then [mlibTerm.False]
        else hol_literals_to_fol (#mapping_parm parm) query
      val () = save_fol_problem (thms, hyps, q)
      val lift = fol_thms_to_hol (#mapping_parm parm) (C assoc axioms) query
      val timed_lift = timed_fn "proof translation" lift
      val timed_stream = map_thk (timed_fn "proof search" o exn_handler)
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

(*
val FOL_TACTIC = fn slv => fn lmap => fn lim => fn goal =>
    let
      val met = Count.mk_meter ()
      val res = FOL_TACTIC slv lmap lim goal
      val {prims,...} = Count.read met
      val _ = chat ("FOL_TACTIC: " ^ Int.toString prims ^ "\n")
    in
      res
    end;
*)

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
   THEN REMOVE_ABBR_TAC
   THEN REPEAT FOL_STRIP_TAC);

(* A flexible tactic that performs normalization of theorems and goal. *)

fun FOL_NORM_TTAC tac ths =
  let
    fun f asms = FOL_NORM (asms @ ths)
  in
    timed_fn "tactic normalization" FOL_NORM_TAC
    THEN POP_ASSUM_LIST (tac o timed_fn "theorem normalization" f)
  end;

(* ------------------------------------------------------------------------- *)
(* Reading in TPTP problems                                                  *)
(* ------------------------------------------------------------------------- *)

(* Mapping first-order formulas to HOL terms *)

local
  open mlibTerm boolSyntax;

  fun h v = Term.mk_var (v, Type.alpha);

  fun g _ (Var v) = h v
    | g ty (Fn (f,a)) =
      let
        val a' = map (g Type.alpha) a
        val ty = Lib.funpow (length a) (fn x => Type.--> (Type.alpha,x)) ty
        val f' = Term.mk_var (f,ty)
      in
        Term.list_mk_comb (f',a')
      end;

  fun f True = T
    | f False = F
    | f (Atom (Fn ("=",[x,y]))) = mk_eq (g Type.alpha x, g Type.alpha y)
    | f (Atom tm) = g Type.bool tm
    | f (Not fm) = mk_neg (f fm)
    | f (And (p,q)) = mk_conj (f p, f q)
    | f (Or (p,q)) = mk_disj (f p, f q)
    | f (Imp (p,q)) = mk_imp (f p, f q)
    | f (Iff (p,q)) = mk_eq (f p, f q)
    | f (Forall (v,p)) = mk_forall (h v, f p)
    | f (Exists (v,p)) = mk_exists (h v, f p);

  val fol_to_hol = f;
in
  val tptp_read = fol_to_hol o mlibTptp.read;
end;

end
