(* ========================================================================= *)
(* HOL NORMALIZATION FUNCTIONS.                                              *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

(*
app load ["BasicProvers", "simpLib", "canon_supportTheory"];
*)

(*
*)
structure canonTools :> canonTools =
struct

open HolKernel Parse boolLib simpLib BasicProvers canon_supportTheory;

infix THEN THENC ORELSEC ++;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ERR f s =
  HOL_ERR
  {message = s, origin_function = f, origin_structure = "canonTools"};

fun distinct [] = true
  | distinct (x :: rest) = not (mem x rest) andalso distinct rest;

fun dest_beq tm =
  let val (a, b, ty) = dest_eq_ty tm
  in if ty = bool then (a, b) else raise ERR "dest_beq" "not a bool"
  end;

val is_beq = can dest_beq;

fun NORM_ASSOC_CONV (a as (is_op, assoc_th)) =
  let
    val rewr = REPEATC (REWR_CONV assoc_th)
  in
    W
    (fn tm =>
     if not (is_op tm) then ALL_CONV
     else rewr THENC BINOP_CONV (NORM_ASSOC_CONV a))
  end;

val CONJ_ASSOC_CONV = NORM_ASSOC_CONV (is_conj, GSYM CONJ_ASSOC);

val DISJ_ASSOC_CONV = NORM_ASSOC_CONV (is_disj, GSYM DISJ_ASSOC);

fun QUANTS_CONV is_quant conv =
  let fun q tm = (if is_quant tm then RAND_CONV (ABS_CONV q) else conv) tm
  in q
  end;

val UNIVERSALS_CONV = QUANTS_CONV is_forall;
val EXISTENTIALS_CONV = QUANTS_CONV is_exists;

fun CONJUNCTS_CONV c =
  let
    fun f tm =
      (if is_conj tm then RATOR_CONV (RAND_CONV c) THENC RAND_CONV f else c) tm
  in
    f
  end;

fun ANTI_BETA_CONV vars tm =
  let
    val tm' = list_mk_comb (list_mk_abs (vars, tm), vars)
    val c = funpow (length vars) (fn c => RATOR_CONV c THENC BETA_CONV) ALL_CONV
  in
    SYM (c tm')
  end;

local
  fun break res [] = res
    | break res (th :: rest) =
    if is_forall (concl th) then break res (SPEC_ALL th :: rest)
    else if is_conj (concl th) then break res (CONJUNCTS th @ rest)
    else break (th :: res) rest;
in
  fun mk_rewrs th = break [] [th];
end;

val canon_ss =
  empty_ss ++
  SIMPSET
  {convs = [{name = "BETA_CONV", trace = 2,
             key = SOME ([], (``(\x:'a. y:'b) z``)), conv = K (K BETA_CONV)}],
   rewrs = [],
   congs = [],
   filter = SOME mk_rewrs,
   ac = [],
   dprocs = []} ;

fun AVOID_SPEC_TAC (tm, v) =
  W (fn (_, g) => SPEC_TAC (tm, variant (free_vars g) v));

(* ------------------------------------------------------------------------- *)
(* Conversion to combinators {S,K,I}.                                        *)
(* ------------------------------------------------------------------------- *)

fun SKI_CONV tm =
  (case dest_term tm of
     CONST _ => ALL_CONV
   | VAR _ => ALL_CONV
   | COMB _ => RAND_CONV SKI_CONV THENC RATOR_CONV SKI_CONV
   | LAMB _
     => ABS_CONV SKI_CONV THENC
        (HO_REWR_CONV MK_K ORELSEC
         HO_REWR_CONV MK_I ORELSEC
         HO_REWR_CONV MK_S) THENC
        SKI_CONV) tm;

(* ------------------------------------------------------------------------- *)
(* Simplifies away applications of the logical connectives to T or F         *)
(* ------------------------------------------------------------------------- *)

val SIMPLIFY_CONV =
  SIMP_CONV canon_ss
  [IMP_CLAUSES, EQ_CLAUSES, OR_CLAUSES, AND_CLAUSES, NOT_CLAUSES,
   FORALL_SIMP, EXISTS_SIMP];

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(* ------------------------------------------------------------------------- *)

val PURE_NNF_CONV =
  SIMP_CONV canon_ss
  [IMP_DISJ_THM, EQ_EXPAND, hd (CONJUNCTS NOT_CLAUSES), NOT_FORALL_THM,
   NOT_EXISTS_THM, DE_MORGAN_THM];

val NNF_CONV = SIMPLIFY_CONV THENC PURE_NNF_CONV;

(* ------------------------------------------------------------------------- *)
(* Skolemization.                                                            *)
(* ------------------------------------------------------------------------- *)

fun PULL_EXISTS_CONV tm =
  ((OR_EXISTS_CONV ORELSEC LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV
    ORELSEC LEFT_OR_EXISTS_CONV ORELSEC RIGHT_OR_EXISTS_CONV ORELSEC
    CHANGED_CONV SKOLEM_CONV) THENC
   TRY_CONV (RAND_CONV (ABS_CONV PULL_EXISTS_CONV))) tm;

val SKOLEMIZE_CONV = DEPTH_CONV PULL_EXISTS_CONV;

(* ------------------------------------------------------------------------- *)
(* A basic tautology prover and simplifier for clauses.                      *)
(* ------------------------------------------------------------------------- *)

local
  fun harvest res [] = res
    | harvest res (tm :: rest) =
    if is_disj tm then
      let val (a, b) = dest_disj tm
      in harvest res (a :: b :: rest)
      end
    else harvest (tm :: res) rest
in
  fun disjuncts tm = harvest [] [tm]
end;

local
  fun prove_case _ [] = raise ERR "TAUTOLOGY_CONV" "argh"
    | prove_case d ((tm, path) :: rest) =
    if is_disj tm then
      let
        val (a, b) = dest_disj tm
      in
        prove_case d ((a, (false, b) :: path) :: (b, (true, a) :: path) :: rest)
      end
    else if tm = d then
      foldl (fn ((true, a), th) => DISJ2 a th | ((false, b), th) => DISJ1 th b)
      (ASSUME d) path
    else prove_case d rest

  fun cases_on d tm =
    let
      val d' = mk_neg d
      val pos_th = prove_case d [(tm, [])]
      val neg_th = prove_case d' [(tm, [])]
    in
      MATCH_MP BOOL_CASES (CONJ (DISCH d pos_th) (DISCH d' neg_th))
    end
in
  fun TAUTOLOGY_CONV tm =
    let
      val (neg, pos) = partition is_neg (disjuncts tm)
    in
      case intersect (map dest_neg neg) pos of [] => NO_CONV tm
      | d :: _ => EQT_INTRO (cases_on d tm)
    end
end;

local
  val simplify_or_f = REWR_CONV OR_F
  val complicate_or_f = REWR_CONV (GSYM OR_F)

  fun contract asms tm =
    (if is_disj tm then contract' asms
     else complicate_or_f THENC contract' asms) tm
  and contract' asms tm =
    let
      val (a, b) = dest_disj tm
      val a' = mk_neg a
      val b_th = DISCH a' (if b = F then REFL F else contract (a :: asms) b)
    in
      if mem a asms then UNDISCH (MATCH_MP CONTRACT_DISJ b_th)
      else CONV_RULE (TRY_CONV (RAND_CONV simplify_or_f))
           (MATCH_MP DISJ_CONGRUENCE b_th)
    end
in
  val CONTRACT_CONV =
    W
    (fn tm =>
     if distinct (disjuncts tm) then NO_CONV
     else DISJ_ASSOC_CONV THENC contract [])
end;

(* ------------------------------------------------------------------------- *)
(* Conjunctive Normal Form.                                                  *)
(* ------------------------------------------------------------------------- *)

val tautology_checking = ref true;

val TSIMP_CONV =
  REWR_CONV OR_T ORELSEC REWR_CONV T_OR ORELSEC
  REWR_CONV AND_T ORELSEC REWR_CONV T_AND ORELSEC
  HO_REWR_CONV FORALL_T;

local
  val r1 = REWR_CONV LEFT_OR_OVER_AND;
  val r2 = REWR_CONV RIGHT_OR_OVER_AND;
  val r3 = HO_REWR_CONV (GSYM LEFT_AND_FORALL_THM);
  val r4 = HO_REWR_CONV (GSYM RIGHT_AND_FORALL_THM);
  val r5 = HO_REWR_CONV FORALL_AND_THM;
  val r6 = HO_REWR_CONV (GSYM LEFT_FORALL_OR_THM);
  val r7 = HO_REWR_CONV (GSYM RIGHT_FORALL_OR_THM);
  val rs = TRY_CONV TSIMP_CONV;
in
  fun PUSH_ORS_CONV tm =
    (TSIMP_CONV ORELSEC
     ((r1 ORELSEC r2 ORELSEC r3 ORELSEC r4 ORELSEC r5) THENC
      BINOP_CONV (TRY_CONV PUSH_ORS_CONV) THENC rs) ORELSEC
     ((r6 ORELSEC r7) THENC QUANT_CONV (TRY_CONV PUSH_ORS_CONV)) ORELSEC
     (if !tautology_checking then (TAUTOLOGY_CONV ORELSEC CONTRACT_CONV)
      else NO_CONV)) tm;
end;

val CLEAN_CNF_CONV =
  EXISTENTIALS_CONV
  (CONJ_ASSOC_CONV THENC
   CONJUNCTS_CONV (UNIVERSALS_CONV DISJ_ASSOC_CONV));

val CNF_CONV =
  SIMPLIFY_CONV THENC NNF_CONV THENC SKOLEMIZE_CONV THENC
  EXISTENTIALS_CONV (DEPTH_CONV PUSH_ORS_CONV) THENC
  CLEAN_CNF_CONV;

(* ------------------------------------------------------------------------- *)
(* Eliminating Hilbert's epsilon operator.                                   *)
(* ------------------------------------------------------------------------- *)

local
  fun get vs tm =
    case 
      (case dest_term tm of COMB (x, y) =>
         (case get vs x of s as SOME _ => s | NONE => get vs y)
       | LAMB (v, b) => get (v :: vs) b
       | _ => NONE) of s as SOME _ => s
       | NONE =>
         if is_select (snd (strip_abs tm)) andalso
           null (intersect (free_vars tm) vs) then SOME tm
         else NONE;
in
  val get_vselect = partial (ERR "get_vselect" "not found") (get []);
end;

local
  fun select_norm vars =
    W
    (SUB_CONV o select_norm o (fn LAMB (v, _) => v :: vars | _ => vars) o
     dest_term) THENC
    W
    (fn tm =>
     if is_select tm then ANTI_BETA_CONV (intersect (free_vars tm) vars)
     else ALL_CONV);
in
  val SELECT_NORM_CONV = select_norm [];
end;

local
  val rewr = RATOR_CONV (REWR_CONV boolTheory.EXISTS_DEF)
  fun conv vars =
    rewr THENC BETA_CONV THENC RAND_CONV (ANTI_BETA_CONV vars) THENC BETA_CONV
in
  fun MK_VSELECT_THM vsel =
    let
      val (vars, sel) = strip_abs vsel
      val (v, body) = dest_select sel
      val ex = mk_exists (v, body)
    in
      foldr (uncurry GEN) (DISCH ex (EQ_MP (conv vars ex) (ASSUME ex))) vars
    end;
end;

fun SPEC_VSELECT_TAC vsel =
  let
    val (v, _) = dest_var (fst (dest_select (snd (strip_abs vsel))))
  in
    MP_TAC (MK_VSELECT_THM vsel) THEN
    AVOID_SPEC_TAC (vsel, mk_var (v, type_of vsel)) THEN
    GEN_TAC
  end;

val SPEC_ONE_SELECT_TAC = W (fn (_, tm) => SPEC_VSELECT_TAC (get_vselect tm));

val SELECT_TAC = CONV_TAC SELECT_NORM_CONV THEN REPEAT SPEC_ONE_SELECT_TAC;

(* ------------------------------------------------------------------------- *)
(* Eliminating lambdas to make terms "as first-order as possible".           *)
(* ------------------------------------------------------------------------- *)

val DELAMB_CONV = SIMP_CONV canon_ss [EQ_LAMB_ELIM, LAMB_EQ_ELIM];

(* ------------------------------------------------------------------------- *)
(* Removing leading existential quantifiers from a theorem.                  *)
(* ------------------------------------------------------------------------- *)

local
  fun comb_beta (x, eq_th) =
    CONV_RULE (RAND_CONV BETA_CONV) (MK_COMB (eq_th, REFL x))
in
  fun EXISTENTIAL_CONST_RULE c_vars th =
    let
      val (c, vars) = strip_comb c_vars
      val sel_th =
        CONV_RULE (RATOR_CONV (REWR_CONV EXISTS_DEF) THENC BETA_CONV) th
      val pred = rator (concl sel_th)
      val def_tm = list_mk_abs (vars, rand (concl sel_th))
      val def_th = ASSUME (mk_eq (c, def_tm))
      val eq_th = MK_COMB (REFL pred, foldl comb_beta def_th vars)
    in
      CONV_RULE BETA_CONV (EQ_MP (SYM eq_th) sel_th)
    end
end;

val NEW_CONST_RULE =
  W (EXISTENTIAL_CONST_RULE o genvar o type_of o bvar o rand o concl);

local
  fun zap _ _ [] = raise ERR "zap" "fresh out of asms"
    | zap th checked (asm::rest) =
    if is_eq asm then
      let
        val (v, def) = dest_eq asm
      in
        if is_var v andalso all (not o free_in v) (checked @ rest) then
          MP (SPEC def (GEN v (DISCH asm th))) (REFL def)
        else zap th (asm::checked) rest
      end
    else zap th (asm::checked) rest
in
  val CLEANUP_CONSTS_RULE = repeat (fn th => zap th [concl th] (hyp th))
end;

(* ------------------------------------------------------------------------- *)
(* Definitional negation normal form                                         *)
(* ------------------------------------------------------------------------- *)

val PURE_DEF_NNF_CONV =
  SIMP_CONV canon_ss
  [IMP_DISJ_THM, NEG_EQ, hd (CONJUNCTS NOT_CLAUSES), NOT_FORALL_THM,
   NOT_EXISTS_THM, DE_MORGAN_THM];

val DEF_NNF_CONV = SIMPLIFY_CONV THENC PURE_DEF_NNF_CONV;

(* ------------------------------------------------------------------------- *)
(* Definitional conjunctive normal form                                      *)
(* ------------------------------------------------------------------------- *)

local
  val conj = Term `$/\ : bool -> bool -> bool`;
  val disj = Term `$\/ : bool -> bool -> bool`;
  val beq = Term `$= : bool -> bool -> bool`;
in
  fun main_cnf defs tm =
    if is_conj tm then def_step defs conj (dest_conj tm)
    else if is_disj tm then def_step defs disj (dest_disj tm)
    else if is_beq tm then def_step defs beq (dest_beq tm)
    else (defs, tm)
  and def_step defs con (a, b) =
    let
      val (defs, a) = main_cnf defs a
      val (defs, b) = main_cnf defs b
      val tm = mk_comb (mk_comb (con, a), b)
    in
      case List.find (fn (_, b) => b = tm) defs of NONE
        => let val g = genvar bool in ((g, tm) :: defs, g) end
      | SOME (v, _) => (defs, v)
    end;
end;

fun PURE_DEF_CNF_CONV tm =
  let
    val (defs, v) = main_cnf [] tm
    val tm' = foldl (fn (d, t) => mk_conj (mk_eq d, t)) v (rev defs)
    val tm' = foldl (fn ((v, _), t) => mk_exists (v, t)) tm' defs
    val rewr = HO_REWR_CONV UNWIND_THM2
    val conv = funpow (length defs) (fn c => QUANT_CONV c THENC rewr) ALL_CONV
    val th = conv tm'
  in
    SYM th
  end;

val DEF_CNF_CONV =
  DEF_NNF_CONV THENC PURE_DEF_CNF_CONV THENC EXISTENTIALS_CONV CNF_CONV;

(* Quick testing
show_assums := true;
try SKI_CONV ``?x. !y. x y = y + 1``;
SKI_CONV ``\x. f x o g``;
SKI_CONV ``\x y. f x y``;
SKI_CONV ``$? = \P. P ($@ P)``;
SKI_CONV ``$==> = \a b. ~a \/ b``;
SKI_CONV ``$! = \P. K T = P``;
SKI_CONV ``!x y. P x y``;
SKI_CONV ``!x y. P y x``;
SKI_CONV ``(P = Q) = (!x. P x = Q x)``;

SIMPLIFY_CONV ``(!x y. P(x) \/ (P(y) /\ F)) ==> (?z. P(z))``;

NNF_CONV ``(!x. P(x)) ==> ((?y. Q(y)) = (?z. P(z) /\ Q(z)))``;
NNF_CONV ``~(~(x = y) = z) = ~(x = ~(y = z))``;

TAUTOLOGY_CONV ``p \/ r \/ ~p \/ ~q``;
CONTRACT_CONV ``(p \/ r) \/ p \/ ~q``;

CNF_CONV ``(p /\ (q \/ r /\ s)) /\ (~p \/ ~q \/ ~s)``;
CNF_CONV ``(p /\ (q \/ r /\ s)) /\ (~p \/ ~q \/ ~s) /\ (p \/ ~p)``;
CNF_CONV ``~(~(x = y) = z) = ~(x = ~(y = z))``;
CNF_CONV ``((p = q) = r) = (p = (q = r))``;
CNF_CONV ``~(((p = q) = r) = (p = (q = r)))``;
CNF_CONV ``?y. x < y ==> (!u. ?v. x * u < y * v)``;
CNF_CONV ``!x. P(x) ==> (?y z. Q(y) \/ ~(?z. P(z) /\ Q(z)))``;
CNF_CONV ``?x y. x + y = 2``;

val p28 =
  ``(!x. P(x) ==> (!x. Q(x))) /\
    ((!x. Q(x) \/ R(x)) ==> (?x. Q(x) /\ R(x))) /\
    ((?x. R(x)) ==> (!x. L(x) ==> M(x))) ==>
    (!x. P(x) /\ L(x) ==> M(x))``;

time CNF_CONV (mk_neg p28);

val p34 =
  ``((?x. !y. P(x) = P(y)) =
     ((?x. Q(x)) = (!y. Q(y)))) =
     ((?x. !y. Q(x) = Q(y)) =
    ((?x. P(x)) = (!y. P(y))))``;

time CNF_CONV (mk_neg p34);

val _ = use "../metis/large-problem.sml";

val large_problem = time Term large_problem_frag;

time CNF_CONV (mk_neg large_problem);

g `!p. 0 = @x. (?y w. (@z. z + w = p + q + y + x) = 2) = (?a b. (@c. c + a = p + q + b + x) < 3)`;
e SELECT_TAC;
drop ();

g `(!x. x IN p ==> (f x = f' x)) ==> ((@x. x IN p /\ f x) = @x. x IN p /\ f' x)`;
e STRIP_TAC;
e (CONV_TAC SELECT_NORM_CONV)
e SELECT_TAC;

EXISTENTIAL_CONST_RULE ``a:'a`` (ASSUME ``?x. (P:'a->'b->'c->bool) x y z``);
EXISTENTIAL_CONST_RULE ``(a:'b->'c->'a) y z``
  (ASSUME ``?x. (P:'a->'b->'c->bool) x y z``);
NEW_CONST_RULE (ASSUME ``?x. (P:'a->'b->'c->bool) x y z``);
CLEANUP_CONSTS_RULE it;

try PURE_DEF_CNF_CONV ``(p /\ (q \/ r /\ s)) /\ (~p \/ ~q \/ ~s)``;
*)

end