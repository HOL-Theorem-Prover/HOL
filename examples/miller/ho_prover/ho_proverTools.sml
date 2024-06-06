structure ho_proverTools :> ho_proverTools =
struct

open HolKernel Parse boolLib BasicProvers;

structure Parse = struct
  open Parse
  val (Type,Term) =
      pred_setTheory.pred_set_grammars
        |> apsnd ParseExtras.grammar_loose_equality
        |> parse_from_grammars
end
open Parse

open Susp combinTheory hurdUtils skiTools;

infixr 0 oo ## ++ << || THENC ORELSEC THENR ORELSER -->;
infix 1 >> |->;
infix thenf orelsef then_frule orelse_frule join_frule;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val !! = REPEAT;

fun trace _ _ = ();
fun printVal _ = ();

val assert = simple_assert;

(* ------------------------------------------------------------------------- *)
(* vterm operations                                                          *)
(* ------------------------------------------------------------------------- *)

local
  fun subsumes ((vars, tm), _) ((_, tm'), _) = can (var_match vars tm) tm'
in
  fun cons_subsume x l =
    if exists (C subsumes x) l then l else x :: filter (not o subsumes x) l
end;

(* ------------------------------------------------------------------------- *)
(* vthm operations                                                           *)
(* ------------------------------------------------------------------------- *)

local
  fun annotate vth = ((I ## concl) vth, vth)
in
  fun vthm_cons_subsume vth vths =
    map snd (cons_subsume (annotate vth) (map annotate vths))
end;

(* ========================================================================= *)
(* Higher-order proof search.                                                *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Types.                                                                    *)
(* ------------------------------------------------------------------------- *)

type literal = bool * term;
datatype clause = CLAUSE of vars * literal list;

datatype fact = FACT of clause * thm susp;

type literal_rule =
  vars * literal -> (substitution * vars * literal list * rule) list;

type clause_rule = clause -> (substitution * clause * rule) list;

type fact_rule = fact -> (substitution * fact) list;

datatype factdb = FACTDB of {factl : fact list, normf : fact_rule};

(* ------------------------------------------------------------------------- *)
(* Literal and clause operations.                                            *)
(* ------------------------------------------------------------------------- *)

fun dest_clause (CLAUSE c) = c;
val clause_vars = fst o dest_clause;
val clause_literals = snd o dest_clause;

fun literal_term (true, tm) = tm
  | literal_term (false, tm) = mk_neg tm;

fun literals_term lits =
  (case map literal_term (rev lits) of [] => F
   | l :: ls => trans (curry mk_disj) l ls);

fun clause_term (CLAUSE ((v, _), lits)) = mk_foralls (v, literals_term lits);

local
  fun canon_ty (_, initial_vars) togo vars ty =
    let
      fun canon 0 vars _ = (0, vars)
        | canon togo vars [] = (togo, vars)
        | canon togo vars (ty :: rest) =
        if is_vartype ty then
          if mem ty vars orelse not (mem ty initial_vars) then
            canon togo vars rest
          else canon (togo - 1) (ty :: vars) rest
        else
          let
            val (_, tys) = dest_type ty
          in
            canon togo vars (tys @ rest)
          end
    in
      canon togo vars [ty]
    end

  fun canon_tm initial_vars tms =
    let
      fun canon _ vars [] = vars
        | canon (0, 0) vars _ = vars
        | canon togo vars (tm :: rest) =
        if is_comb tm then
          let
            val (a, b) = dest_comb tm
          in
            canon togo vars (a :: b :: rest)
          end
        else
          let
            val (tmtogo, tytogo) = togo
            val (tmvars, tyvars) = vars
            val (tytogo', tyvars') =
              canon_ty initial_vars tytogo tyvars (type_of tm)
          in
            if is_tmvar initial_vars tm andalso not (tmem tm tmvars) then
              canon (tmtogo - 1, tytogo') (tm :: tmvars, tyvars') rest
            else canon (tmtogo, tytogo') (tmvars, tyvars') rest
          end
    in
      canon ((length ## length) initial_vars) empty_vars tms
    end
in
  fun clause_canon_vars (CLAUSE (vars, lits)) =
    CLAUSE (canon_tm vars (map snd lits), lits);
end;

(* ------------------------------------------------------------------------- *)
(* Fact and proof operations.                                                *)
(* ------------------------------------------------------------------------- *)

fun dest_fact (FACT f) = f;
val fact_clause = fst o dest_fact;
val fact_vars = clause_vars o fact_clause;
val fact_literals = clause_literals o fact_clause;

local
  val thm1 = prove (``!a. a ==> ~a ==> F``, PROVE_TAC [])
  val thm2 = prove (``!x. (~x ==> F) ==> x``, PROVE_TAC [])
in
  val norm_thm = MATCH_MP thm1 THENR UNDISCH
  fun march_literal lit = DISCH (mk_neg (literal_term lit)) THENR MATCH_MP thm2
end;

local
  fun mk_fact (vars, th) =
    let
      val c = CLAUSE (vars, [(true, concl th)])
    in
      FACT (c, delay (K (norm_thm th)))
    end;
in
  val vthm_to_fact = mk_fact o (I ## CONV_RULE SKI_CONV)
  val thm_to_fact = vthm_to_fact o thm_to_vthm;
end;

fun fact_to_vthm (FACT (cl, thk)) = (clause_vars cl, force thk);
val fact_to_thm = vthm_to_thm o fact_to_vthm;

(* ------------------------------------------------------------------------- *)
(* Fact rule operations.                                                     *)
(* ------------------------------------------------------------------------- *)

val no_frule : fact_rule = fn _ => raise ERR "no_frule" "always fails";
val all_frule : fact_rule = fn f => [(empty_subst, f)];
val empty_frule : fact_rule = K [];

val trace_frule : fact_rule =
  fn f =>
  let
    val _ = trace "trace_frule: f" (fn () => printVal f)
  in
    [(empty_subst, f)]
  end;

fun op orelse_frule (r1 : fact_rule, r2 : fact_rule) : fact_rule =
  r1 orelsef r2;

fun op then_frule (r1 : fact_rule, r2 : fact_rule) : fact_rule =
  let
    fun process (sub, f) = map (refine_subst sub ## I) (r2 f)
  in
    flatten o map process o r1
  end;

fun try_frule r = r orelse_frule all_frule;

fun op join_frule (r1 : fact_rule, r2 : fact_rule) : fact_rule =
  op@ o ((r1 orelse_frule empty_frule) ## (r2 orelse_frule empty_frule)) o D;

fun repeat_frule r f = try_frule (r then_frule repeat_frule r) f;

fun joinl_frule [] = no_frule
  | joinl_frule (r :: rest) = r join_frule (joinl_frule rest);

fun first_frule [] = no_frule
  | first_frule (r :: rest) = r orelse_frule (first_frule rest);

local
  fun reassem previous next (sub, vars, lits, vf) =
    let
      val previous' = map (I ## pinst sub) (rev previous)
      val next' = map (I ## pinst sub) next
    in
      (sub, CLAUSE (vars, previous' @ lits @ next'), vf)
    end
  handle (h as HOL_ERR _) => raise err_BUG "lrule_to_crule" h

  fun mk_crule _ _ _ [] = raise ERR "lrule_to_crule" "lrule does not apply"
    | mk_crule r vars previous (lit :: next) =
    (case total r (vars, lit) of NONE => mk_crule r vars (lit :: previous) next
     | SOME cls' => map (reassem previous next) cls')
in
  fun lrule_to_crule (lrule : literal_rule) : clause_rule =
    fn CLAUSE (vars, lits) => mk_crule lrule vars [] lits
end;

fun crule_to_frule (crule : clause_rule) : fact_rule =
  fn FACT (cl, th) =>
  let
    fun process (sub, cl', vf) =
      let
        val _ = trace "crule_to_frule: cl'" (fn () => printVal cl')
      in
        (sub, FACT (cl', susp_map vf th))
      end
    handle (h as HOL_ERR _) => raise err_BUG "crule_to_frule" h
    val cls' = crule cl
    val _ =
      trace "crule_to_frule: ((cl, th), cls')"
      (fn () => printVal ((cl, th), cls'))
    val res = map process cls'
  in
    res
  end;

val lrule_to_frule = crule_to_frule o lrule_to_crule;

(* Replace clause variables in a fact with fresh ones.                   *)
(* In order to avoid cyclic substitutions and to facilitate unification, *)
(* we INSIST that variables present in facts are always fresh.           *)
(* Designers of tactic rules may thus wish to use this rule liberally.   *)

val fresh_vars_crule : clause_rule =
  fn CLAUSE (vars, lits) =>
  let
    val (vars', (sub, _)) = new_vars vars
  in
    [(sub, CLAUSE (vars', map (I ## pinst sub) lits), PINST sub)]
  end;

val fresh_vars_frule : fact_rule = crule_to_frule fresh_vars_crule;

(* ------------------------------------------------------------------------- *)
(* Fact database operations.                                                 *)
(* ------------------------------------------------------------------------- *)

val null_factdb = FACTDB {factl = [], normf = no_frule};

fun dest_factdb (FACTDB db) = db;
val factdb_factl = #factl o dest_factdb;
val factdb_normf = #normf o dest_factdb;

val factdb_size = length o factdb_factl;

fun factdb_norm_frule (FACTDB {normf, ...}) = repeat_frule normf;

fun factdb_norm db f = map snd (factdb_norm_frule db f);

fun factdb_add_fact f (db as FACTDB {factl, normf}) =
  FACTDB {factl = factdb_norm db f @ factl, normf = normf};

val factdb_add_facts = C (trans factdb_add_fact);

val factdb_add_vthm = factdb_add_fact o vthm_to_fact;
val factdb_add_vthms = C (trans factdb_add_vthm);

val factdb_add_thm = factdb_add_fact o thm_to_fact;
val factdb_add_thms = C (trans factdb_add_thm);

local
  fun norm_app normf normf' =
    (normf then_frule try_frule normf') orelse_frule normf';
in
  fun factdb_add_norm normf' (FACTDB {factl, normf}) =
    factdb_add_facts factl (FACTDB {factl = [], normf = norm_app normf normf'});
end;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

val pp_literal = pp_map literal_term pp_term;

val genvar_prefix = "%%genvar%%";
fun dest_genvar v =
  let
    val (name, ty) = dest_var v
    val _ = assert (String.isPrefix genvar_prefix name)
      (ERR "dest_genvar" "not a genvar")
  in
    (string_to_int (String.extract (name, size genvar_prefix, NONE)), ty)
  end;
val is_genvar = can dest_genvar;

fun clause_pretty_term (CLAUSE ((vs, _), lits)) =
  let
    val tm = literals_term lits
    val gs = (filter is_genvar o free_vars) tm
    fun pretty_g g =
      let
        val name =
          (int_to_string o fst o dest_genvar) g
          handle HOL_ERR _ => (fst o dest_var) g
        val stem = if tmem g vs then "v" else "c"
      in
        mk_var (stem ^ "_" ^ name, type_of g)
      end

    val sub = (subst o zipwith (curry op|->) gs o map pretty_g) gs
  in
    mk_foralls (map sub vs, sub tm)
  end;

val pp_clause = pp_map clause_pretty_term pp_term;

val pp_fact = pp_map (fn FACT (c, p) => c) pp_clause;

val pp_factdb = pp_map factdb_factl (pp_list pp_fact);

(* ------------------------------------------------------------------------- *)
(* Rewriting for facts.                                                      *)
(* ------------------------------------------------------------------------- *)

fun sub_conv (rw, RW) =
  (fn tm =>
   let
     val (a, b) = dest_comb tm
   in
     case Df (total rw) (a, b) of (SOME a', SOME b') => mk_comb (a', b')
     | (SOME a', NONE) => mk_comb (a', b)
     | (NONE, SOME b') => mk_comb (a, b')
     | (NONE, NONE) => raise ERR "sub_conv" "unchanged"
   end,
   fn tm =>
   let
     val (a, b) = dest_comb tm
   in
     case Df (total (QCONV RW)) (a, b) of (SOME a', SOME b') => MK_COMB (a', b')
     | (SOME a', NONE) => MK_COMB (a', REFL b)
     | (NONE, SOME b') => MK_COMB (REFL a, b')
     | (NONE, NONE) => raise ERR "sub_conv" "unchanged"
   end);

fun once_depth_conv (rw, RW) =
  (fn tm => (rw orelsef (fst (sub_conv (once_depth_conv (rw, RW))))) tm,
   fn tm => QCONV (RW ORELSEC (snd (sub_conv (once_depth_conv (rw, RW))))) tm);

fun redepth_conv (rw, RW) =
  (fn tm =>
   ((fst (sub_conv (redepth_conv (rw, RW))) orelsef rw)
    thenf repeatf rw
    thenf tryf (fst (redepth_conv (rw, RW)))) tm,
   fn tm =>
   QCONV
   ((snd (sub_conv (redepth_conv (rw, RW))) ORELSEC RW)
    THENC REPEATC RW
    THENC TRYC (snd (redepth_conv (rw, RW)))) tm);

fun top_depth_conv (rw, RW) =
  (fn tm =>
   (((repeatplusf rw thenf
      tryf (fst (sub_conv (top_depth_conv (rw, RW))))) orelsef
     (fst (sub_conv (top_depth_conv (rw, RW))))) thenf
    tryf (fst (top_depth_conv (rw, RW)))) tm,
   fn tm =>
   QCONV
   (((REPEATPLUSC RW THENC
      TRYC (snd (sub_conv (top_depth_conv (rw, RW))))) ORELSEC
     (snd (sub_conv (top_depth_conv (rw, RW))))) THENC
    TRYC (snd (top_depth_conv (rw, RW)))) tm);

fun rewr_conv vths =
  let
    val rewrs = map (fn (vars, th) => ((vars, LHS th), (RHS th, th))) vths
    val d = mk_ski_discrim rewrs
    val _ = trace "rewr_conv: d" (fn () => printVal (dest_ski_discrim d))
    fun lookup tm =
      (case ski_discrim_match d tm of [] => raise ERR "rewrs_conv" "unchanged"
       | a :: _ => a)
    val rw = (fn (sub, (r, _)) => pinst sub r) o lookup
    val RW = (fn (sub, (_, th)) => PINST sub th) o lookup
    fun rw' tm =
      let
        val _ = trace "rewr_conv: rw: tm" (fn () => printVal tm)
        val res = rw tm
        val _ = trace "rewr_conv: rw: res" (fn () => printVal res)
      in
        res
      end
    fun RW' tm =
      let
        val _ = trace "rewr_conv: RW: tm" (fn () => printVal tm)
        val res = QCONV RW tm
        val _ = trace "rewr_conv: RW: res" (fn () => printVal res)
      in
        res
      end
  in
    (rw', RW')
  end;

val rewrite_conv = top_depth_conv o rewr_conv;
val once_rewrite_conv = once_depth_conv o rewr_conv;

fun conv_to_lconv (rw, RW) (lit as (pos, tm)) =
  let
    val _ = trace "literal_conv: lit" (fn () => printVal lit)
    val res1 = (pos, rw tm) : literal
    val _ = trace "literal_conv: res1" (fn () => printVal res1)
    val res2 =
      march_literal lit THENR
      CONV_RULE ((if pos then I else RAND_CONV) RW) THENR
      norm_thm
    fun res2' th =
      let
        val _ = trace "conv_to_lconv: th" (fn () => printVal th)
        val th' = res2 th
        val _ = trace "conv_to_lconv: th'" (fn () => printVal th')
      in
        th'
      end
  in
    (res1, res2')
  end;

fun lconv_to_crule lconv : clause_rule =
  let
    fun advance lit (changed, lits', rules') =
      (case total lconv lit of NONE => (changed, lit :: lits', rules')
       | SOME (lit', rule') => (true, lit' :: lits', rules' THENR rule'))
  in
    fn cl as CLAUSE (vars, lits) =>
    (case trans advance (false, [], ALL_RULE) lits of (false, _, _)
       => raise ERR "clause_conv" "unchanged"
     | (true, lits', rule') =>
       let
         val cl' = CLAUSE (vars, rev lits')
         val _ = trace "lconv_to_cconv: (cl, cl')" (fn () => printVal (cl, cl'))
         val res = [(empty_subst, cl', rule')]
       in
         res
       end)
  end;

val rewrite_frule =
  crule_to_frule o lconv_to_crule o conv_to_lconv o rewrite_conv;

val once_rewrite_frule =
  crule_to_frule o lconv_to_crule o conv_to_lconv o once_rewrite_conv;

(* ------------------------------------------------------------------------- *)
(* Normalization has two parts: basic rewrites and rules of inference.       *)
(*                                                                           *)
(* The basic rewrites define the relationship between the combinators,       *)
(* and between the constants of the logic; an example is: !x. ~~x = x.       *)
(*                                                                           *)
(* The rules of inference propagate truth from the object level to the       *)
(* meta level; an example of this is the "conjunction" rule that takes as    *)
(* input a theorem of the form a /\ b; and outputs two theorems: a and b.    *)
(* ------------------------------------------------------------------------- *)

(* First, the basic rewrites *)

val basic_rewrites =
  map (prove o (I ## (fn ths => !! FUN_EQ_TAC ++ RW_TAC bool_ss ths)))
  [(``!x y z. S x y z = (x z) (y z)``, [S_DEF]),
   (``!x y z. combin$C x y z = x z y``, [C_DEF]),
   (``!x y z. (x o y) z = x (y z)``, [o_DEF]),
   (``!x y. K x y = x``, [K_DEF]),
   (``!x. I x = x``, [I_THM]),
   (``!x y. S (K x) (K y) = K (x y)``, [S_DEF, K_DEF]),
   (``!x. S (K x) = $o x``, [S_DEF, K_DEF, o_DEF]),
   (``S o K = $o``, [S_DEF, K_DEF, o_DEF]),
   (``!x y. S x (K y) = combin$C x y``, [S_DEF, K_DEF, C_DEF]),
   (``!x y. x o (K y) = K (x y)``, [K_DEF, o_DEF]),
   (``!x y. combin$C (K x) y = K (x y)``, [K_DEF, C_DEF]),
   (``!x y. K x o y = K x``, [K_DEF, o_DEF]),
   (``!x. x o I = x``, [I_THM, o_DEF]),
   (``$o I = I``, [I_THM, o_DEF]),
   (``S K K = I``, [I_THM, S_DEF, K_DEF]),
   (``!x y z. (x o y) o z = x o (y o z)``, [o_THM]),
   (``!x. (x = T) = x``, []),
   (``!x. (T = x) = x``, []),
   (``!x. (x = F) = ~x``, []),
   (``!x. (F = x) = ~x``, []),
   (``!x:bool. ~~x = x``, []),
   (``!x y z w. w (if x then y else z) = if x then w y else w z``, []),
   (``!x y z w. (if x then y else z) w = if x then y w else z w``, []),
   (``!x y. (x ==> y) = (~x \/ y)``, [IMP_DISJ_THM]),
   (``!x. (x = x) = T``, []),
   (``!x y. (x = y) = (!z. x z = y z)``, []),
   (``!x y. (x = y) = (x ==> y) /\ (y ==> x)``, [EQ_IMP_THM]),
   (``!x y z. (if x then y else z) = (x ==> y) /\ (~x ==> z)``, [])];

val basic_rewrite_frule =
  rewrite_frule (map ((I ## CONV_RULE SKI_CONV) o thm_to_vthm) basic_rewrites);

(* Second, the basic rules of inference. *)

local
  val thm1 = prove (``!x. ~~x ==> x``, PROVE_TAC [])
in
  val neg_lrule : literal_rule =
    fn (vars, lit as (pos, tm)) =>
    let
      val body = dest_neg tm
    in
      [(empty_subst, vars, [(not pos, body)],
        if pos then ALL_RULE
        else march_literal lit THENR MATCH_MP thm1 THENR norm_thm)]
    end

  val neg_frule = lrule_to_frule neg_lrule
end;

local
  val thm1 = prove (``~T ==> F``, PROVE_TAC [])
in
  val true_lrule : literal_rule =
    fn (vars, lit as (pos, tm)) =>
    let
      val _ = assert (Teq tm) (ERR "true_lrule" "term not T")
    in
      if pos then []
      else [(empty_subst, vars, [], march_literal lit THENR MATCH_MP thm1)]
    end

  val true_frule = lrule_to_frule true_lrule
end;

val false_lrule : literal_rule =
  fn (vars, lit as (pos, tm)) =>
  let
    val _ = assert (Feq tm) (ERR "false_lrule" "term not F")
  in
      if pos then [(empty_subst, vars, [], march_literal lit)] else []
  end;

val false_frule = lrule_to_frule false_lrule

local
  val thm1 = prove (``!a b. (a \/ b) ==> ~a ==> ~b ==> F``, PROVE_TAC [])
  val thm2 = prove (``!a b. ~(a \/ b) ==> ~~a ==> F``, PROVE_TAC [])
  val thm3 = prove (``!a b. ~(a \/ b) ==> ~~b ==> F``, PROVE_TAC [])
in
  val disj_lrule : literal_rule =
    fn (vars, lit as (pos, tm)) =>
    let
      val (a, b) = dest_disj tm
    in
      if pos then
        [(empty_subst, vars, [(true, a), (true, b)],
          march_literal lit THENR MATCH_MP thm1 THENR UNDISCH THENR UNDISCH)]
      else
        [(empty_subst, vars, [(false, a)],
          march_literal lit THENR MATCH_MP thm2 THENR UNDISCH),
         (empty_subst, vars, [(false, b)],
          march_literal lit THENR MATCH_MP thm3 THENR UNDISCH)]
    end

  val disj_frule = lrule_to_frule disj_lrule
end;

local
  val thm1 = prove (``!a b. ~(a /\ b) ==> ~~a ==> ~~b ==> F``, PROVE_TAC [])
  val thm2 = prove (``!a b. (a /\ b) ==> ~a ==> F``, PROVE_TAC [])
  val thm3 = prove (``!a b. (a /\ b) ==> ~b ==> F``, PROVE_TAC [])
in
  val conj_lrule : literal_rule =
    fn (vars, lit as (pos, tm)) =>
    let
      val (a, b) = dest_conj tm
    in
      if pos then
        [(empty_subst, vars, [(true, a)],
          march_literal lit THENR MATCH_MP thm2 THENR UNDISCH),
         (empty_subst, vars, [(true, b)],
          march_literal lit THENR MATCH_MP thm3 THENR UNDISCH)]
      else
        [(empty_subst, vars, [(false, a), (false, b)],
          march_literal lit THENR MATCH_MP thm1 THENR UNDISCH THENR UNDISCH)]
    end

  val conj_frule = lrule_to_frule conj_lrule
end;

local
  fun mk_c ty [] = genvar ty
    | mk_c ty (v :: vs) = mk_comb (mk_c (type_of v --> ty) vs, v)

  fun var_literal vars atom =
    let
      val lvar = (genvar o fst o dom_rng o type_of) atom
      val atom' = mk_comb (atom, lvar)
    in
      (lvar, (cons lvar ## I) vars, atom')
    end;

  fun const_literal vars atom =
    let
      val ctype = (fst o dom_rng o type_of) atom
      val tm_vars = op_intersect aconv (fst vars) (free_vars atom)
      val cvar = mk_c ctype tm_vars
      val atom' = mk_comb (atom, cvar)
    in
      (cvar, atom')
    end;

  fun true_forall_th lvar =
    CONV_RULE (RAND_CONV GENVAR_ETA_EXPAND_CONV)
    THENR SPEC lvar
    THENR norm_thm

  fun false_forall_th cvar =
    CONV_RULE
    (RAND_CONV (RAND_CONV GENVAR_ETA_EXPAND_CONV) THENC NOT_FORALL_CONV)
    THENR NEW_CONST_RULE cvar
    THENR norm_thm

  fun false_exists_th lvar =
    CONV_RULE
    (RAND_CONV (RAND_CONV GENVAR_ETA_EXPAND_CONV) THENC NOT_EXISTS_CONV)
    THENR SPEC lvar
    THENR norm_thm

  fun true_exists_th cvar =
    CONV_RULE (RAND_CONV GENVAR_ETA_EXPAND_CONV)
    THENR NEW_CONST_RULE cvar
    THENR norm_thm
in
  val forall_lrule : literal_rule =
    fn (vars, lit as (pos, atom)) =>
    let
      val body = dest_unaryop "!" atom
    in
      if pos then
        let
          val (lvar, vars', atom') = var_literal vars body
        in
          [(empty_subst, vars', [(pos, atom')],
            march_literal lit THENR true_forall_th lvar)]
        end
      else
        let
          val (cvar, atom') = const_literal vars body
        in
          [(empty_subst, vars, [(pos, atom')],
            march_literal lit THENR false_forall_th cvar)]
        end
    end

  val exists_lrule : literal_rule =
    fn (vars, lit as (pos, atom)) =>
    let
      val body = dest_unaryop "?" atom
    in
      if pos then
        let
          val (cvar, atom') = const_literal vars body
        in
          [(empty_subst, vars, [(pos, atom')],
            march_literal lit THENR true_exists_th cvar)]
        end
      else
        let
          val (lvar, vars', atom') = var_literal vars body
        in
          [(empty_subst, vars', [(pos, atom')],
            march_literal lit THENR false_exists_th lvar)]
        end
    end

  val forall_frule = lrule_to_frule forall_lrule
  val exists_frule = lrule_to_frule exists_lrule
end;

local
  val thm1 = prove
    (``(p : bool -> 'a) x = if x then p T else p F``, RW_TAC bool_ss []);
  val (p_tm, x_tm) = dest_comb (LHS thm1)
  val rhs_thm1 = RHS thm1

  fun get_sub tm =
    let
      val (a, b) = dest_comb tm
      val (dom, rng) = dom_rng (type_of a)
      val _ = assert (dom = bool) (ERR "bool_lrule" "not a bool")
      val _ = assert (b !~ T andalso b !~ F) (ERR "bool_rule" "already T or F")
      val ty_sub = if rng = alpha then [alpha |-> rng] else []
      val (tm_sub, ty_sub) =
        norm_subst (([p_tm |-> a, x_tm |-> b], empty_tmset), (ty_sub, []))
    in
      (tm_sub, ty_sub)
    end;

  val rewr = (C pinst rhs_thm1 o get_sub, C PINST thm1 o get_sub)

  val lconv = conv_to_lconv (once_depth_conv rewr);
in
  val bool_lrule : literal_rule =
    fn (vars, lit) =>
    let
      val (lit', r) = lconv lit
    in
      [(empty_subst, vars, [lit'], r)]
    end

  val bool_frule = lrule_to_frule bool_lrule
end;

local
  val thm1 = prove (``!(x : 'a). ~(x = x) ==> F``, PROVE_TAC [])
in
  val equal_lrule : literal_rule =
    fn (vars, lit as (pos, atom)) =>
    let
      val _ = assert (not pos) (ERR "equal_lrule" "positive term")
      val (l, r) = dest_eq atom
    in
      if is_tmvar vars l then
        let
          val _ = assert (not (free_in l r)) (ERR "equal_lrule" "l free in r")
          val sub = ([l |-> r], [])
        in
          [(sub, vars_after_subst vars sub, [],
            march_literal lit THENR PINST sub THENR MATCH_MP thm1)]
        end
      else if is_tmvar vars r then
        let
          val _ = assert (not (free_in r l)) (ERR "equal_lrule" "r free in l")
          val sub = ([r |-> l], [])
        in
          [(sub, vars_after_subst vars sub, [],
            march_literal lit THENR PINST sub THENR MATCH_MP thm1)]
        end
      else raise ERR "equal_rule" "non-var = non-var"
    end

  val equal_frule = lrule_to_frule equal_lrule
end;

local
  fun merge _ [] = raise ERR "factor_rule" "nothing to do"
    | merge dealt ((lit as (pos, atom)) :: rest) =
    if op_mem xtm_eq (not pos, atom) dealt then NONE
    else if op_mem xtm_eq lit dealt then SOME (rev dealt @ rest)
    else merge (lit :: dealt) rest

  fun process _ NONE = []
    | process vars (SOME lits) = [(empty_subst, CLAUSE (vars, lits), ALL_RULE)]
in
  val merge_crule : clause_rule =
    fn CLAUSE (vars, lits) => process vars (merge [] lits);

  val merge_frule = crule_to_frule merge_crule
end;

val basic_cnf_frule : fact_rule =
  first_frule
  [neg_frule, true_frule, false_frule, disj_frule, conj_frule,
   forall_frule, exists_frule, bool_frule, equal_frule, merge_frule];

(* ------------------------------------------------------------------------- *)
(* The fundamental factdb.                                                   *)
(* ------------------------------------------------------------------------- *)

val empty_factdb =
  (factdb_add_norm basic_cnf_frule o
   factdb_add_norm basic_rewrite_frule)
  null_factdb;

val mk_factdb = trans factdb_add_thm empty_factdb;

(* ------------------------------------------------------------------------- *)
(* Fact `tactic' rules for open-ended proof search.                          *)
(* ------------------------------------------------------------------------- *)

(* A resolution rule. *)

local
  fun extra f =
    let
      val (vars, lits) = dest_clause (fact_clause f)
      fun part (true, atom) (ts, fs) = (((vars, atom), f) :: ts, fs)
        | part (false, atom) (ts, fs) = (ts, ((vars, atom), f) :: fs)
      val (ts, fs) = trans part ([], []) lits
    in
      (ts, fs)
    end;

  fun add f (td, fd) =
    let
      val (ts, fs) = extra f
    in
      (ski_discrim_addl ts td, ski_discrim_addl fs fd)
    end;
in
  fun mk_atom_db db =
    trans add (empty_ski_discrim, empty_ski_discrim) (factdb_factl db)
end;

val mk_pos_atom_db = fst o mk_atom_db;
val mk_neg_atom_db = snd o mk_atom_db;

local
  val thm1 = prove (``!x. x /\ ~x ==> F``, PROVE_TAC [])
in
  fun resolution_rule sub (pos, atom) th th' =
    let
      val atom' = pinst sub atom
      val (s_th, s_th') = Df (PINST sub) (th, th')
      val _ =
        trace "resolution rule: ((pos, atom'), s_th, s_th')"
        (fn () => printVal ((pos, atom'), s_th, s_th'))
      val sm_th = march_literal (pos, atom') s_th
      val sm_th' = march_literal (not pos, atom') s_th'
      val _ =
        trace "resolution rule: (sm_th, sm_th')"
        (fn () => printVal (sm_th, sm_th'))
    in
      MATCH_MP thm1 (if pos then CONJ sm_th sm_th' else CONJ sm_th' sm_th)
    end

  fun lazy_resolution_rule sub atom thk thk' =
    susp_map (uncurry (resolution_rule sub atom)) (pair_susp thk thk')
end;

local
  fun process vars lit (sub, f as FACT (CLAUSE (vars', lits'), thk')) =
    let
      val res_vars =
        vars_union (vars_after_subst vars sub) (vars_after_subst vars' sub)
      val lit' = (not ## pinst sub) lit
      val res_lits = (filter (not o xtm_eq lit') o map (I ## pinst sub)) lits'
    in
      (sub, res_vars, res_lits,
       fn th => resolution_rule sub lit th (force thk'))
    end
in
  fun pos_resolution_lrule neg_db : literal_rule =
    fn (vars, lit as (pos, atom)) =>
    let
      val _ = assert pos (ERR "pos_resolution_rule" "not a positive literal")
      val matches = ski_discrim_unify neg_db (vars, atom)
      val _ =
        trace "pos_resolution_lrule: ((vars, lit), matches)"
        (fn () => printVal ((vars, lit), matches))
      val res = map (process vars lit) matches
      val _ = trace "pos_resolution_lrule: res" (fn () => printVal res)
    in
      res
    end;

  fun neg_resolution_lrule pos_db : literal_rule =
    fn (vars, lit as (pos, atom)) =>
    let
      val _ =
        assert (not pos) (ERR "neg_resolution_rule" "not a negative literal")
      val matches = ski_discrim_unify pos_db (vars, atom)
      val _ =
        trace "neg_resolution_lrule: ((vars, lit), matches)"
        (fn () => printVal ((vars, lit), matches))
      val res = map (process vars lit) matches
      val _ = trace "neg_resolution_lrule: res" (fn () => printVal res)
    in
      res
    end;
end;

fun pos_resolution_frule neg_db : fact_rule =
  lrule_to_frule (pos_resolution_lrule neg_db);

fun neg_resolution_frule pos_db : fact_rule =
  lrule_to_frule (neg_resolution_lrule pos_db);

fun biresolution_frule db : fact_rule =
  let
    val (pos_db, neg_db) = mk_atom_db db
  in
    pos_resolution_frule neg_db join_frule neg_resolution_frule pos_db
  end;

(* K rules *)

fun collect_funvars vars tm =
  let
    fun fvars res [] = res
      | fvars res (tm :: rest) =
      if is_comb tm then
        let
          val (a, b) = dest_comb tm
          val res' = if is_tmvar vars a then op_insert aconv a res else res
        in
          fvars res' (a :: b :: rest)
        end
      else fvars res rest
    val res = fvars [] [tm]
    val _ =
      trace "collect_funvars: ((vars, tm), res)"
      (fn () => printVal ((vars, tm), res))
  in
    res
  end;

local
  fun k_set_var vars (pos, atom) v =
    let
      val (dom, rng) = dom_rng (type_of v)
      val k =
        mk_thy_const {Name = "K", Thy = "combin", Ty = rng --> dom --> rng}
      val g = genvar rng
      val res = mk_comb (k, g)
      val sub = ([v |-> res], [])
      val vars' = (cons g ## I) (vars_after_subst vars sub)
    in
      (sub, vars', [(pos, pinst sub atom)], PINST sub)
    end
  handle (h as HOL_ERR _) => raise err_BUG "k_set_var" h
in
  val k1_lrule : literal_rule =
    fn (vars, (pos, atom)) =>
    let
      val funvars = collect_funvars vars atom
    in
      map (k_set_var vars (pos, atom)) funvars
    end
  handle (h as HOL_ERR _) => raise err_BUG "k1_lrule" h
end;

val k1_frule = lrule_to_frule k1_lrule;

(* S rules *)

local
  fun s_set_var vars (lit as (pos, atom)) v =
    let
      val v_type = type_of v
      val (dom, rng) = dom_rng v_type
      val inter = gen_tyvar ()
      val g1_type = dom --> inter --> rng
      val g1 = genvar g1_type
      val g2_type = dom --> inter
      val g2 = genvar g2_type
      val s = mk_const ("S", g1_type --> g2_type --> v_type)
      val res = mk_comb (mk_comb (s, g1), g2)
      val sub = ([v |-> res], [])
      val vars' =
        ((cons g1 o cons g2) ## cons inter) (vars_after_subst vars sub)
      val _ =
        trace "s_set_var: (vars, sub, vars')"
        (fn () => printVal (vars, sub, vars'))
      val lit' = (pos, pinst sub atom)
      val _ = trace "s_set_var: (lit, lit')" (fn () => printVal (lit, lit'))
    in
      (sub, vars', [lit'], PINST sub)
    end
  handle (h as HOL_ERR _) => raise err_BUG "s_set_var" h
in
  val s1_lrule : literal_rule =
    fn (vars, (pos, atom)) =>
    let
      val funvars = collect_funvars vars atom
      val res = map (s_set_var vars (pos, atom)) funvars
    in
      res
    end
  handle (h as HOL_ERR _) => raise err_BUG "s1_lrule" h
end;

val s1_frule = lrule_to_frule s1_lrule;

(* A variable-at-top-level rule *)

(* A variable-in-equality rule *)

local
  val thm1 = prove (``!x. ~(x = x) ==> F``, PROVE_TAC []);
in
  val equality_lrule : literal_rule =
    fn (vars, lit as (pos, atom)) =>
    let
      val _ = assert (not pos) (ERR "equality_lrule" "positive literal")
      val (a, b) = dest_eq atom
      val sub = ski_unify vars a b
      val _ =
        trace "equality_lrule: ((vars, lit), sub)"
        (fn () => printVal ((vars, lit), sub))
      val vars' = vars_after_subst vars sub
    in
      [(sub, vars', [], march_literal lit THENR PINST sub THENR MATCH_MP thm1)]
    end;
end;

val equality_frule : fact_rule = lrule_to_frule equality_lrule;

(* A paramodulation rule from the equality perspective *)

(* A paramodulation rule from the term perspective *)

local
  val thm1 = prove (``!x y : bool. (x = y) ==> (~x = ~y)``, PROVE_TAC []);
in
  fun paramodulation_rule (lit as (pos, _)) sub eq_th th =
    let
      val _ =
        trace "paramodulation_rule: (lit, sub, eq_th, th)"
        (fn () => printVal (lit, sub, eq_th, th))
      val res =
        (march_literal lit THENR PINST sub THENR
         EQ_MP ((if pos then ALL_RULE else MATCH_MP thm1) eq_th) THENR
         norm_thm) th
      val _ = trace "paramodulation_rule: res" (fn () => printVal res)
    in
      res
    end
  handle h as HOL_ERR _ => raise err_BUG "paramodulation_rule" h;
end;

local
  val thm1 = prove (``!x y. (x = y) ==> (y = x)``, PROVE_TAC []);

  fun extra1 (sub, vars', eq, lits, rule, th) =
    (sub, vars', rhs eq, lits, rule, th);

  fun extra2 (sub, vars', eq, lits, rule, th) =
    (sub, vars', lhs eq, lits, rule THENR MATCH_MP thm1, th);

  fun process vars eq (sub, FACT (CLAUSE (vars', lits), th)) =
    let
      val res_vars =
        vars_union (vars_after_subst vars sub) (vars_after_subst vars' sub)
      val res_eq = pinst sub eq
      val res_lits =
        filter (not o xtm_eq (true, res_eq)) (map (I ## pinst sub) lits)
      val _ = assert (length res_lits < length lits)
        (BUG "paramodulation" "literal length check failed")
    in
      (sub, res_vars, res_eq, res_lits,
       PINST sub THENR march_literal (true, res_eq), th)
    end
    handle h as HOL_ERR _ => raise err_BUG "paramodulation.process" h;

  fun find_matches pos_db vars tm =
    let
      val ty = type_of tm
      val g = genvar ty
      val vars' = (cons g ## I) vars
      val eq1 = mk_eq (tm, g)
      val res1 = ski_discrim_unify pos_db (vars', eq1)
      val eq2 = mk_eq (g, tm)
      val res2 = ski_discrim_unify pos_db (vars', eq2)
      val all_matches =
        map (extra1 o process vars' eq1) res1 @
        map (extra2 o process vars' eq2) res2
      val _ =
        trace "paramodulation.find_matches: ((vars, tm), all_matches)"
        (fn () => printVal ((vars, tm), all_matches))
    in
      all_matches
    end
    handle h as HOL_ERR _ => raise err_BUG "paramodulation.find_matches" h;

  fun left_lift_para b (sub, vars', a', lits, rule, thk) =
    let
      val b' = pinst sub b
    in
      (sub, vars', mk_comb (a', b'), lits,
       fn th => MK_COMB (rule th, REFL b'), thk)
    end
    handle h as HOL_ERR _ => raise err_BUG "paramodulation.left_lift_para" h;

  fun right_lift_para a (sub, vars', b', lits, rule, thk) =
    let
      val a' = pinst sub a
    in
      (sub, vars', mk_comb (a', b'), lits,
       fn th => MK_COMB (REFL a', rule th), thk)
    end
    handle h as HOL_ERR _ => raise err_BUG "paramodulation.right_lift_para" h;

  fun perform_para pos_db vars =
    let
      fun para tm =
        (let
          val (a, b) = dest_comb tm
         in
           map (left_lift_para b) (para a) @
           map (right_lift_para a) (para b)
         end
         handle HOL_ERR _ => []) @
        (find_matches pos_db vars tm)
    in
      para
    end
    handle h as HOL_ERR _ => raise err_BUG "paramodulation.perform_para" h;

  fun finalize (lit as (pos, _)) (sub, vars', atom', lits', rule, thk) =
    (sub, vars', (pos, atom') :: lits',
     fn th => paramodulation_rule lit sub (rule (force thk)) th)
    handle h as HOL_ERR _ => raise err_BUG "paramodulation.finalize" h;
in
  fun paramodulation_lrule pos_db : literal_rule =
    fn (vars, lit as (pos, atom)) =>
    let
      val res = map (finalize lit) (perform_para pos_db vars atom)
      val _ =
        trace "paramodulation_lrule: ((vars, lit), res)"
        (fn () => printVal ((vars, lit), res))
    in
      res
    end
  handle h as HOL_ERR _ => raise err_BUG "paramodulation_lrule" h;
end;

fun paramodulation_frule db : fact_rule =
  lrule_to_frule (paramodulation_lrule (mk_pos_atom_db db))
  handle h as HOL_ERR _ => raise err_BUG "paramodulation_frule" h;

(* ------------------------------------------------------------------------- *)
(* The core engine.                                                          *)
(* ------------------------------------------------------------------------- *)

(* prune_subfacts_wrt: using only the most general results wrt some term. *)

fun prune_subfacts_wrt tm l =
  let
    val _ =
      trace "prune_subfacts_wrt: (tm, length l)"
      (fn () => printVal ((tm, length l)))
    fun tag (f as (sub, FACT (CLAUSE (vars, _), _))) = ((vars, pinst sub tm), f)
    val res = map snd (trans cons_subsume [] (map tag l))
    val _ =
      trace "prune_subfacts_wrt: (tm, length l, length res)"
      (fn () => printVal ((tm, length l, length res)))
  in
    res
  end;

local
  type state = literal list * (substitution * fact);

  exception CUT of string;

  (* Ancestor resolution *)

  fun anc_res_frule (a_pos, a_atom) : fact_rule =
    fn FACT (CLAUSE (vars, [(pos, atom)]), thk) =>
    let
      val _ = assert (a_pos <> pos) (ERR "anc_frule" "same polarity")
      val sub = ski_unify vars a_atom atom
      val vars' = vars_after_subst vars sub
      val thk' = susp_map (PINST sub) thk
    in
      [(sub, FACT (CLAUSE (vars', []), thk'))]
    end
    | _ => raise BUG "anc_frule" "panic";

  val ancs_res_frule = joinl_frule o map anc_res_frule;
in
  fun meson_frule_reduce_depth (reduce : fact_rule) =
    let
      fun meson _ res ([] : state list) = res
        | meson depth res
        ((_, f as (sub, FACT (CLAUSE (vars, []), _))) :: others) =
        if can (invert_subst vars) sub then [f]
        else meson depth (f :: res) others
        | meson depth res
        ((state as
          (ancs, (sub, goal as FACT (CLAUSE (vars, lit :: lits), thk)))) ::
         others) =
        let
          val _ =
            trace "meson: (depth, state, length others)"
            (fn () => printVal ((depth, state, length others)))
          val _ = trace "meson: sub" (fn () => printVal sub)
          val _ = trace "meson: goal" (fn () => printVal goal)
          val _ = assert (depth > 0) (CUT "hit bottom")
          val _ = assert (not (op_mem xtm_eq lit ancs)) (CUT "duplicate goal")
          val goal1 = FACT (CLAUSE (vars, [lit]), thk)
          val subgoals =
            map
            ((fn (a, (s, f)) => (map (I ## pinst s) a, (s, f))) o
             add_fst (lit :: ancs))
            ((ancs_res_frule ancs join_frule reduce) goal1)
          val _ =
            trace "meson: (goal1, map snd subgoals)"
            (fn () => printVal (goal1, map snd subgoals))
          val subresults =
            prune_subfacts_wrt (snd lit) (meson (depth - 1) [] subgoals)
          fun mp (sub', FACT (CLAUSE (vars', []), thk')) =
            (map (I ## pinst sub') ancs,
             (refine_subst sub sub',
              FACT (CLAUSE (vars', map (I ## pinst sub') lits),
                    lazy_resolution_rule sub' lit thk thk')))
            | mp _ = raise BUG "meson mp" "panic"
          val newgoals = map mp subresults
          val _ =
            trace "meson: (state, subgoals, subresults, newgoals)"
            (fn () => printVal (state, subgoals, subresults, newgoals))
          val _ =
            trace "meson: map (snd o snd) newgoals"
            (fn () => printVal (map (snd o snd) newgoals))
        in
          meson depth res (newgoals @ others)
        end
        handle CUT _ => meson depth res others
    in
      fn depth => fn f => meson depth [] [([], (empty_subst, f))]
    end
    handle (h as HOL_ERR _) => raise err_BUG "meson_frule_depth_frule" h;
end;

fun meson_refute_reduce_depth_fact reduce depth =
  let
    val frule =
      fresh_vars_frule then_frule
      meson_frule_reduce_depth reduce depth
  in
    fn f =>
    let
      val _ = trace "meson_refute_fact_reduce_depth: f" (fn () => printVal f)
      val res =
        case frule f of []
          => raise ERR "meson_refute_fact_reduce_depth" "too deep"
        | ((_, f) :: _)
          => ZAP_CONSTS_RULE (snd (fact_to_vthm f))
    in
      res
    end
  end;

fun meson_refute_reduce_depth db reduce depth =
  let
    val _ = trace "meson_refute_reduce_depth: depth" (fn () => printVal depth)
    val reduce' = reduce then_frule try_frule (factdb_norm_frule db)
    val f = meson_refute_reduce_depth_fact reduce depth
    val res =
      case partial_first (total f) (factdb_factl db) of NONE
        => raise ERR "meson_refute_reduce_depth" "too deep!"
      | SOME th => th
    val _ = trace "meson_refute_reduce_depth: res" (fn () => printVal res)
  in
    res
  end;

fun meson_refute_reduce_deepen db reduce =
  let
    val _ = trace "meson_refute_reduce_deepen: db" (fn () => printVal db)
    val refute = meson_refute_reduce_depth db reduce
  in
    fn start => fn step =>
    let
      fun deepen 0 depth =
        raise ERR "meson_refute_deepen" "no solutions up to max depth"
        | deepen n depth = (refute orelsef (deepen (n - 1) o plus step)) depth
    in
      C deepen start
    end
  end;

local
  fun post goal (sub, f) =
    let
      val (vars, th) = fact_to_vthm f
      val rule = CCONTR (pinst sub goal) THENR ZAP_CONSTS_RULE
    in
      (sub, (vars, rule th))
    end

  fun post_process goal = map (post goal) o prune_subfacts_wrt goal
in
  fun meson_prove_reduce_depth db reduce depth (vars, goal) =
    let
      val _ = trace "meson_prove_reduce_depth: db" (fn () => printVal db)
      val _ =
        trace "meson_prove_reduce_depth: (vars, goal)"
        (fn () => printVal (vars, goal))
      val neg_goal = mk_neg goal
      val input = vthm_to_fact (vars, ASSUME neg_goal)
      val frule =
        fresh_vars_frule then_frule
        try_frule (factdb_norm_frule db) then_frule
        meson_frule_reduce_depth reduce depth
      val res = (post_process goal o frule) input
      val _ =
        trace "meson_prove_reduce_depth: ((vars, goal), res)"
        (fn () => printVal ((vars, goal), res))
    in
      res
    end
  handle (h as HOL_ERR _) => raise err_BUG "meson_prove_reduce_depth" h;
end;

(* ------------------------------------------------------------------------ *)
(* The HOL tactic                                                           *)
(* ------------------------------------------------------------------------ *)

(* Tuning parameters *)

val prover_depth = ref 3;
val prover_start = ref 1;
val prover_step = ref 1;
val prover_steps = ref 10;

(* The higher-order fact rule we use *)

fun ho_meson_frule db : fact_rule =
  joinl_frule
  [biresolution_frule db then_frule fresh_vars_frule,
   paramodulation_frule db then_frule fresh_vars_frule,
   equality_frule, k1_frule, s1_frule] then_frule
  try_frule (factdb_norm_frule db);

(* The calls to meson with the rule and default depths *)

fun ho_refute db =
  meson_refute_reduce_deepen db (ho_meson_frule db) (!prover_start)
  (!prover_step) (!prover_steps);

fun ho_prove db vgoal =
  meson_prove_reduce_depth db (ho_meson_frule db) (!prover_depth) vgoal;

(* Simple strip tac to reduce the problem before beginning *)

val ho_PROVE_INITIAL_TAC = REPEAT (EQ_TAC || STRIP_TAC);

(* The tactic *)

fun ho_PROVE_TAC ths =
  ho_PROVE_INITIAL_TAC
  ++ CCONTR_TAC
  ++ EVERY (map ASSUME_TAC ths)
  ++ ASSUM_LIST (ACCEPT_TAC o ho_refute o mk_factdb);

(* A more convenient entry point to the tactic for general proving *)

fun ho_PROVE ths goal = prove (goal, ho_PROVE_TAC ths);

(* test goals

allow_trace "vterm_to_ski_patterns";
allow_trace "literal_conv";
allow_trace "rewr_conv";
allow_trace "fact_conv";
allow_trace "ski_discrim_unify";
allow_trace "resolution";
allow_trace "collect_funvars";
allow_trace "equality_lrule";
allow_trace "crule_to_frule";
allow_trace "conv_to_lconv";
allow_trace "lconv_to_cconv";
allow_trace "s_set_var";
allow_trace "paramodulation";
allow_trace "meson: (goal1, map (snd o snd) subgoals)";
allow_trace "";
reset_traces ();
allow_trace "meson";
deny_trace "meson:";

tt2 ho_PROVE [] ``!a. F ==> a``;
tt2 ho_PROVE [] ``!a. a ==> a``;
tt2 ho_PROVE [] ``!x y : bool. (x \/ ~y) /\ (~x \/ y) /\ P x ==> P y``;
tt2 ho_PROVE [] ``?guy. drinks guy ==> (!people : 'pub. drinks people)``;
tt2 ho_PROVE [] ``P 3 \/ ?x. (x = 3) /\ ~P 3``;
tt2 ho_PROVE [] ``P c /\ (!a. P a ==> Q a) ==> Q c``;
tt2 ho_PROVE [] ``~?a b. (a \/ b) /\ (~a \/ b) /\ (a \/ ~b) /\ (~a \/ ~b)``;
tt2 ho_PROVE [] ``!a b c. ~(~(a = b) = c) = ~(a = ~(b = c))``;
tt2 ho_PROVE [] ``!(a : bool) b. P a /\ (a = b) ==> P b``;
tt2 ho_PROVE [] ``(!x. x IN s ==> x IN t /\ x IN u) =
  (!x. x IN s ==> x IN t) /\ !x. x IN s ==> x IN u``;
tt2 ho_PROVE [] ``?x. !y. x y = 1 + y``;
tt2 ho_PROVE [] ``?x. !y. x y = y + 1``;
tt2 ho_PROVE [] ``?x. x a b c = (a c) (b c)``;
tt2 ho_PROVE [] ``!P a b. (a = b) /\ P a ==> P b``;
tt2 ho_PROVE [] ``!a b. ?x : 'a. P a \/ P b ==> P x``;
tt2 ho_PROVE [] ``(!se : num. ?n : num. f n se se) ==> ?m : num. f m 0 0 ``;
tt2 ho_PROVE [] ``(!x : 'a. F0 a x \/ !y. F0 x y) ==> ?x. !y. F0 x y``;
tt2 ho_PROVE []
  ``((a : 'a = b) \/ (c = d)) /\ ((a = c) \/ (b = d)) ==> (a = d) \/ (b = c)``;
tt2 ho_PROVE [] ``!a b : bool. (a = b) ==> (P a = P b)``;
tt2 ho_PROVE [] ``!a b. (a ==> b) /\ (b ==> a) ==> (P a = P b)``;

(* bugs?
tt2 ho_PROVE [INTER_FINITE, INTER_COMM]
  ``!s. FINITE s ==> !t. FINITE (t INTER s)``;
tt2 ho_PROVE [LENGTH_NIL] ``LENGTH ([]:num list) = 0``;
tt2 ho_PROVE [IN_EMPTY] ``x IN {}``;
*)

(*
tt2 ho_PROVE [] ``?x. !a. x a = a``;
tt2 ho_PROVE [] ``?x. !a b c. x a b c = (a c) (b c)``;
tt2 ho_PROVE []
  ``!(f : 'a -> 'c) (g : 'a -> 'b).
       (!x y. (g x = g y) ==> (f x = f y)) ==> (?h. !x. h (g x) = f x)``;
tt2 ho_PROVE [] ``?x. !a b. a ==> b = x a b``;
tt2 ho_PROVE [] ``?x. !a b. b ==> a = x a b``;
tt2 ho_PROVE [] ``?x. !a b. (b = a) = x a b``;
*)

(* Difficult bug produced by cyclic substitutions *)
tt2 ho_PROVE [] ``(!x. y = g (c x)) ==> (?z. y = g z)``;

(* Eric *)
tt2 ho_PROVE []
  ``!P Q R. !x : 'a. ?v w. !y (z : 'b).
      P x /\ Q y ==> (P v \/ R w) /\ (R z ==> Q v)``;

(* I think this needs paramodulation-from-the-equality-perspective
val P49 =
  ``(?x y. !z : 'a. (z = x) \/ (z = y)) /\
    P a /\ P b /\ ~(a = b) ==> !x : 'a. P x``;
tt2 ho_PROVE [] P49;
*)

(* Los : this takes 116s, must reduce this somehow...
val LOS =
  ``(!x y z. P x y /\ P y z ==> P x z) /\
    (!x y z. Q x y /\ Q y z ==> Q x z) /\
    (!x y. P x y ==> P y x) /\
    (!x y. P x y \/ Q x y) ==>
    (!x y. P x y) \/ (!x y. Q x y)``;
tt2 PROVE [] `^LOS`;
tt2 ho_PROVE [] LOS;
*)

(* Equality-free Agatha *)
tt2 ho_PROVE []
  ``lives(agatha) /\ lives(butler) /\ lives(charles) /\
    (killed(agatha,agatha) \/ killed(butler,agatha) \/
     killed(charles,agatha)) /\
    (!x y. killed(x,y) ==> hates(x,y) /\ ~richer(x,y)) /\
    (!x. hates(agatha,x) ==> ~hates(charles,x)) /\
    (hates(agatha,agatha) /\ hates(agatha,charles)) /\
    (!x. lives(x) /\ ~richer(x,agatha) ==> hates(butler,x)) /\
    (!x. hates(agatha,x) ==> hates(butler,x)) /\
    (!x. ~hates(x,agatha) \/ ~hates(x,butler) \/ ~hates(x,charles)) ==>
    (?x : 'person. killed(x,agatha))``;

(* Agatha
tt2 ho_PROVE []
  ``(?x : 'a. lives x /\ killed x agatha) /\
    (lives agatha /\ lives butler /\ lives charles) /\
    (!x. lives x ==> (x = agatha) \/ (x = butler) \/ (x = charles)) /\
    (!y x. killed x y ==> hates x y) /\
    (!x y. killed x y ==> ~richer x y) /\
    (!x. hates agatha x ==> ~hates charles x) /\
    (!x. ~(x = butler) ==> hates agatha x) /\
    (!x. ~richer x agatha ==> hates butler x) /\
    (!x. hates agatha x ==> hates butler x) /\
    (!x. ?y. ~hates x y) /\
    ~(agatha = butler) ==>
    killed agatha agatha``;
*)

(* The steamroller
tt2 ho_PROVE []
  ``((!x:'a. P1 x ==> P0 x) /\ (?x. P1 x)) /\
    ((!x. P2 x ==> P0 x) /\ (?x. P2 x)) /\
    ((!x. P3 x ==> P0 x) /\ (?x. P3 x)) /\
    ((!x. P4 x ==> P0 x) /\ (?x. P4 x)) /\
    ((!x. P5 x ==> P0 x) /\ (?x. P5 x)) /\
    ((?x. Q1 x) /\ (!x. Q1 x ==> Q0 x)) /\
    (!x. P0 x ==> (!y. Q0 y ==> R x y) \/
     (((!y. P0 y /\ S0 y x /\ ?z. Q0 z /\ R y z) ==> R x y))) /\
    (!x y. P3 y /\ (P5 x \/ P4 x) ==> S0 x y) /\
    (!x y. P3 x /\ P2 y ==> S0 x y) /\
    (!x y. P2 x /\ P1 y ==> S0 x y) /\
    (!x y. P1 x /\ (P2 y \/ Q1 y) ==> ~(R x y)) /\
    (!x y. P3 x /\ P4 y ==> R x y) /\
    (!x y. P3 x /\ P5 y ==> ~(R x y)) /\
    (!x. (P4 x \/ P5 x) ==> ?y. Q0 y /\ R x y) ==>
    ?x y. P0 x /\ P0 y /\ ?z. Q1 z /\ R y z /\ R x y``;
*)

(* Unskolemized Melham *)
tt2 ho_PROVE []
  ``(!x y. (g x = g y) ==> (f x = f y)) ==>
    (!y. ?h. !x. (y = g x) ==> (h = f x))``;

(* Full Melham *)
val lemma = tt prove
  (``!(f : 'a -> 'c) (g : 'a -> 'b).
        (!x y. (g x = g y) ==> (f x = f y)) ==>
        ?h. !y x. (y = g x) ==> (h y = f x)``,
   !! STRIP_TAC
   (*the following should work, but doesn't, so we use the below instead
   ++ Ho_rewrite.PURE_REWRITE_TAC [GSYM Ho_boolTheory.SKOLEM_THM]*)
   ++ MP_TAC (Q.ISPEC `\ (y : 'b) (hy : 'c). !x. (y = g x) ==> (hy = f x)`
              (GSYM Ho_boolTheory.SKOLEM_THM))
   ++ BETA_TAC
   ++ DISCH_THEN (ho_REWRITE_TAC o wrap)
   ++ ho_PROVE_TAC []);

val MELHAM = tt prove
  (``!(f : 'a -> 'c) (g : 'a -> 'b).
       (!x y. (g x = g y) ==> (f x = f y)) ==>
       (?h. !x. h (g x) = f x)``,
   ho_PROVE_TAC [lemma]);

(* A couple of token prove goals *)

tt2 ho_prove (mk_factdb [ASSUME ``P (c : 'a) : bool``,
                            ASSUME ``?x : 'a. P x``])
(([``y : 'a``], []), ``P (y : 'a) : bool``);

tt2 ho_prove empty_factdb
(([``x : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c``], []),
 ``(x : ('a -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'c) a b c = (a c) (b c)``);

end of test goals *)


(* non-interactive mode
*)
end;
