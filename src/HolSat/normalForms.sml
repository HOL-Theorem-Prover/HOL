(* ========================================================================= *)
(* HOL NORMALIZATION FUNCTIONS.                                              *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

(*
app load ["BasicProvers", "simpLib", "numLib"];
*)

(*
*)
structure normalForms :> normalForms =
struct

open HolKernel Parse boolLib simpLib numLib BasicProvers;

infix THEN THENC ORELSEC ++ --> |->;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

fun ERR f s =
  HOL_ERR
  {message = s, origin_function = f, origin_structure = "normalForms"};

fun distinct [] = true
  | distinct (x :: rest) = not (mem x rest) andalso distinct rest;

val if_and_only_if = ``$= : bool->bool->bool``;

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

fun CONJUNCTS_CONV c =
  let fun f tm = (if is_conj tm then LAND_CONV c THENC RAND_CONV f else c) tm
  in f
  end;

fun ANTI_BETA_CONV vars tm =
  let
    val tm' = list_mk_comb (list_mk_abs (vars, tm), vars)
    val c = funpow (length vars) (fn c => RATOR_CONV c THENC BETA_CONV) ALL_CONV
  in
    SYM (c tm')
  end;

fun AVOID_SPEC_TAC (tm, v) =
  W (fn (_, g) => SPEC_TAC (tm, variant (free_vars g) v));

fun STRIP_EXISTS_CONV c tm =
  if is_exists tm then STRIP_QUANT_CONV c tm else c tm;

fun STRIP_FORALL_CONV c tm =
  if is_forall tm then STRIP_QUANT_CONV c tm else c tm;

(* ------------------------------------------------------------------------- *)
(* Replace genvars with variants on `v`.                                     *)
(*                                                                           *)
(* Example:                                                                  *)
(*   ?%%genvar%%20744 %%genvar%%20745 %%genvar%%20746.                       *)
(*     (%%genvar%%20744 \/ %%genvar%%20745 \/ ~%%genvar%%20746) /\           *)
(*     (%%genvar%%20746 \/ ~%%genvar%%20744) /\                              *)
(*     (%%genvar%%20746 \/ ~%%genvar%%20745) /\ (~q \/ ~%%genvar%%20745) /\  *)
(*     (r \/ ~%%genvar%%20745) /\ (%%genvar%%20745 \/ q \/ ~r) /\            *)
(*     (q \/ ~p \/ ~%%genvar%%20744) /\ (p \/ ~q \/ ~%%genvar%%20744) /\     *)
(*     (%%genvar%%20744 \/ ~p \/ ~q) /\ (%%genvar%%20744 \/ p \/ q) /\       *)
(*     %%genvar%%20746                                                       *)
(*   =                                                                       *)
(*   ?v v1 v2.                                                               *)
(*     (v \/ v1 \/ ~v2) /\ (v2 \/ ~v) /\ (v2 \/ ~v1) /\ (q \/ ~v1) /\        *)
(*     (r \/ ~v1) /\ (v1 \/ ~q \/ ~r) /\ (q \/ ~p \/ ~v) /\                  *)
(*     (p \/ ~q \/ ~v) /\ (v \/ ~p \/ ~q) /\ (v \/ p \/ q) /\ v2             *)
(* ------------------------------------------------------------------------- *)

local
  datatype ('a, 'b) sum = INL of 'a | INR of 'b;

  fun ren _ [tm] [] = tm
    | ren avoid (b :: a :: dealt) (INL NONE :: rest) =
    ren avoid (mk_comb (a, b) :: dealt) rest
    | ren avoid (b :: dealt) (INL (SOME v) :: rest) =
    ren avoid (mk_abs (v, b) :: dealt) rest
    | ren avoid dealt (INR (sub, tm) :: rest) =
    (case dest_term tm of
       CONST _ => ren avoid (tm :: dealt) rest
     | VAR _ => ren avoid (subst sub tm :: dealt) rest
     | COMB (a, b) =>
       ren avoid dealt (INR (sub, a) :: INR (sub, b) :: INL NONE :: rest)
     | LAMB (v, b) =>
       let
         val (v', sub') =
           if not (is_genvar v) then (v, sub) else
             let val v' = variant avoid (mk_var ("v", type_of v))
             in (v', (v |-> v') :: sub)
             end
       in
         ren (insert v' avoid) dealt (INR (sub', b) :: INL (SOME v') :: rest)
       end)
    | ren _ _ _ = raise ERR "readable_vars" "BUG";
in
  fun readable_vars tm = ren (all_vars tm) [] [INR ([], tm)];
end;

fun READABLE_VARS_CONV tm =
  ALPHA tm (Lib.with_flag (Globals.priming, SOME "") readable_vars tm);

(* ------------------------------------------------------------------------- *)
(* Conversion to combinators {S,K,I}.                                        *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (?f. !y. f y = y + 1)                                                   *)
(*   =                                                                       *)
(*   $? (S (K $!) (S (S (K S) (S (K (S (K $=))) I)) (K (S $+ (K 1)))))       *)
(* ------------------------------------------------------------------------- *)

val MK_S = prove
  (``!x y. (\v. (x v) (y v)) = S x y``,
   REPEAT STRIP_TAC THEN
   CONV_TAC (FUN_EQ_CONV) THEN
   RW_TAC boolSimps.bool_ss [combinTheory.S_DEF, combinTheory.K_DEF]);

val MK_K = prove
  (``!x. (\v. x) = K x``,
   REPEAT STRIP_TAC THEN
   CONV_TAC (FUN_EQ_CONV) THEN
   RW_TAC boolSimps.bool_ss [combinTheory.S_DEF, combinTheory.K_DEF]);

val MK_I = prove
  (``(\v. v) = I``,
   REPEAT STRIP_TAC THEN
   CONV_TAC (FUN_EQ_CONV) THEN
   RW_TAC boolSimps.bool_ss
   [combinTheory.S_DEF, combinTheory.K_DEF, combinTheory.I_THM]);
   
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
(* Beta reduction and simplifying boolean rewrites.                          *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (!x y. P x \/ (P y /\ F)) ==> ?z. P z                                   *)
(*   =                                                                       *)
(*   (!x. P x) ==> ?z. P z                                                   *)
(* ------------------------------------------------------------------------- *)

val simplify_ss = simpLib.++ (pureSimps.pure_ss, boolSimps.BOOL_ss);

val SIMPLIFY_CONV = SIMP_CONV simplify_ss [];

(* ------------------------------------------------------------------------- *)
(* Negation normal form.                                                     *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (!x. P x) ==> ((?y. Q y) = ?z. P z /\ Q z)                              *)
(*   =                                                                       *)
(*   ((?y. Q y) /\ (?z. P z /\ Q z) \/ (!y. ~Q y) /\ !z. ~P z \/ ~Q z) \/    *)
(*   ?x. ~P x                                                                *)
(* ------------------------------------------------------------------------- *)

val IMP_DISJ_THM' = prove
  (``!x y. x ==> y = y \/ ~x``,
   PROVE_TAC []);

val PURE_NNF_CONV =
  SIMP_CONV simplify_ss
  [IMP_DISJ_THM', EQ_EXPAND, hd (CONJUNCTS NOT_CLAUSES), NOT_FORALL_THM,
   NOT_EXISTS_THM, DE_MORGAN_THM];

val NNF_CONV = SIMPLIFY_CONV THENC PURE_NNF_CONV;

(* ------------------------------------------------------------------------- *)
(* Skolemization.                                                            *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (!x. (?y. Q y \/ !z. ~P z \/ ~Q z) \/ ~P x)                             *)
(*   =                                                                       *)
(*   ?y. !x. (Q (y x) \/ !z. ~P z \/ ~Q z) \/ ~P x                           *)
(* ------------------------------------------------------------------------- *)

fun PULL_EXISTS_CONV tm =
  ((OR_EXISTS_CONV ORELSEC LEFT_AND_EXISTS_CONV ORELSEC RIGHT_AND_EXISTS_CONV
    ORELSEC LEFT_OR_EXISTS_CONV ORELSEC RIGHT_OR_EXISTS_CONV ORELSEC
    CHANGED_CONV SKOLEM_CONV) THENC
   TRY_CONV (RAND_CONV (ABS_CONV PULL_EXISTS_CONV))) tm;

val SKOLEMIZE_CONV = DEPTH_CONV PULL_EXISTS_CONV;

(* ------------------------------------------------------------------------- *)
(* A basic tautology prover and simplifier for clauses                       *)
(*                                                                           *)
(* Examples:                                                                 *)
(*   TAUTOLOGY_CONV:   p \/ r \/ ~p \/ ~q   =  T                             *)
(*   CONTRACT_CONV:    (p \/ r) \/ p \/ ~q  =  p \/ r \/ ~q                  *)
(* ------------------------------------------------------------------------- *)

val BOOL_CASES = prove
  (``!a b. (a ==> b) /\ (~a ==> b) ==> b``,
   PROVE_TAC []);

val T_OR = prove
  (``!t. T \/ t = T``,
   PROVE_TAC []);

val OR_T = prove
  (``!t. t \/ T = T``,
   PROVE_TAC []);

val T_AND = prove
  (``!t. T /\ t = t``,
   PROVE_TAC []);

val AND_T = prove
  (``!t. t /\ T = t``,
   PROVE_TAC []);

val FORALL_T = prove
  (``(!x. T) = T``,
   PROVE_TAC []);

val OR_F = prove
  (``!t. t \/ F = t``,
   PROVE_TAC []);

val CONTRACT_DISJ = prove
  (``!a b b'. (~a ==> (b = b')) ==> (~a ==> (a \/ b = b'))``,
   PROVE_TAC []);

val DISJ_CONGRUENCE = prove
  (``!a b b'. (~a ==> (b = b')) ==> (a \/ b = a \/ b')``,
   PROVE_TAC []);

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
(*                                                                           *)
(* Example:                                                                  *)
(*   (!x. P x ==> ?y z. Q y \/ ~?z. P z /\ Q z)                              *)
(*   =                                                                       *)
(*   ?y. !x x'. Q (y x) \/ ~P x' \/ ~Q x' \/ ~P x                            *)
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
  val p1 = r1 ORELSEC r2 ORELSEC r3 ORELSEC r4 ORELSEC r5
  val p2 = r6 ORELSEC r7
  val p3 = TAUTOLOGY_CONV ORELSEC CONTRACT_CONV
  val ps = TRY_CONV TSIMP_CONV;
in
  fun PUSH_ORS_CONV tm =
    (TSIMP_CONV ORELSEC
     (p1 THENC BINOP_CONV (TRY_CONV PUSH_ORS_CONV) THENC ps) ORELSEC
     (p2 THENC QUANT_CONV (TRY_CONV PUSH_ORS_CONV) THENC ps) ORELSEC
     (if !tautology_checking then p3 else NO_CONV)) tm;
end;

val CLEAN_CNF_CONV =
  STRIP_EXISTS_CONV
  (CONJ_ASSOC_CONV THENC
   CONJUNCTS_CONV (STRIP_FORALL_CONV DISJ_ASSOC_CONV));

val CNF_CONV =
  SIMPLIFY_CONV THENC NNF_CONV THENC SKOLEMIZE_CONV THENC
  STRIP_EXISTS_CONV (DEPTH_CONV PUSH_ORS_CONV) THENC
  CLEAN_CNF_CONV;

(* ------------------------------------------------------------------------- *)
(* Definitional negation normal form                                         *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ((~p = (~q = r)) = ((p = q) = r))                                       *)
(* ------------------------------------------------------------------------- *)

val NEG_EQ = prove
  (``!a b. ~(a = b) = (~a = b)``,
   PROVE_TAC []);

val PURE_DEF_NNF_CONV =
  SIMP_CONV simplify_ss
  [IMP_DISJ_THM, NEG_EQ, hd (CONJUNCTS NOT_CLAUSES), NOT_FORALL_THM,
   NOT_EXISTS_THM, DE_MORGAN_THM];

val DEF_NNF_CONV = SIMPLIFY_CONV THENC PURE_DEF_NNF_CONV;

(* ------------------------------------------------------------------------- *)
(* Definitional conjunctive normal form                                      *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ?v v' v'' v''' v''''.                                                   *)
(*     (v''' \/ ~v' \/ ~v'''') /\ (v' \/ ~v''' \/ ~v'''') /\                 *)
(*     (v'''' \/ ~v' \/ ~v''') /\ (v'''' \/ v' \/ v''') /\                   *)
(*     (r \/ ~v'' \/ ~v''') /\ (v'' \/ ~r \/ ~v''') /\                       *)
(*     (v''' \/ ~v'' \/ ~r) /\ (v''' \/ v'' \/ r) /\ (q \/ ~p \/ ~v'') /\    *)
(*     (p \/ ~q \/ ~v'') /\ (v'' \/ ~p \/ ~q) /\ (v'' \/ p \/ q) /\          *)
(*     (v \/ p \/ ~v') /\ (~p \/ ~v \/ ~v') /\ (v' \/ p \/ ~v) /\            *)
(*     (v' \/ ~p \/ v) /\ (r \/ q \/ ~v) /\ (~q \/ ~r \/ ~v) /\              *)
(*     (v \/ q \/ ~r) /\ (v \/ ~q \/ r) /\ v''''                             *)
(* ------------------------------------------------------------------------- *)

val EQ_DEFCNF = prove
  (``!x y z.
       (x = (y = z)) =
       (z \/ ~y \/ ~x) /\ (y \/ ~z \/ ~x) /\ (x \/ ~y \/ ~z) /\ (x \/ y \/ z)``,
   CONV_TAC CNF_CONV);

val AND_DEFCNF = prove
  (``!x y z. (x = (y /\ z)) = (y \/ ~x) /\ (z \/ ~x) /\ (x \/ ~y \/ ~z)``,
   CONV_TAC CNF_CONV);

val OR_DEFCNF = prove
  (``!x y z. (x = (y \/ z)) = (y \/ z \/ ~x) /\ (x \/ ~y) /\ (x \/ ~z)``,
   CONV_TAC CNF_CONV);

fun sub_cnf f con defs (a, b) =
    let
      val (defs, a) = f defs a
      val (defs, b) = f defs b
      val tm = mk_comb (mk_comb (con, a), b)
    in
      (defs, tm)
    end;

fun def_step (defs, tm) =
  case List.find (fn (_, b) => b = tm) defs of NONE
    => let val g = genvar bool in ((g, tm) :: defs, g) end
  | SOME (v, _) => (defs, v);

fun gen_cnf defs tm =
  if is_conj tm then
    def_step (sub_cnf gen_cnf conjunction defs (dest_conj tm))
  else if is_disj tm then
    def_step (sub_cnf gen_cnf disjunction defs (dest_disj tm))
  else if is_beq tm then
    def_step (sub_cnf gen_cnf if_and_only_if defs (dest_beq tm))
  else
    (defs, tm);

fun disj_cnf defs tm =
  if is_disj tm then sub_cnf disj_cnf disjunction defs (dest_disj tm)
  else gen_cnf defs tm;

fun conj_cnf defs tm =
  if is_conj tm then sub_cnf conj_cnf conjunction defs (dest_conj tm)
  else disj_cnf defs tm;

(* Natural rule
val ONE_POINT_CONV = HO_REWR_CONV UNWIND_THM2;
*)

(* An attempt to soup it up
*)
fun ONE_POINT_CONV tm =
  let
    val (v, t) = dest_exists tm
    val (q, b) = dest_conj t
    val (_, d) = dest_eq q
    val th = SPEC d (ISPEC (mk_abs (v, b)) UNWIND_THM2)
  in
    CONV_RULE
    (LAND_CONV (QUANT_CONV (RAND_CONV BETA_CONV)) THENC RAND_CONV BETA_CONV) th
  end;

fun PURE_DEF_CNF_CONV tm =
  let
    val (defs, tm) = conj_cnf [] tm
    val (vs, eqs) = unzip (map (fn (v, d) => (v, mk_eq (v, d))) (rev defs))
    val tm = list_mk_exists (vs, foldl mk_conj tm eqs)
    fun push c = QUANT_CONV c THENC ONE_POINT_CONV
    val th = funpow (length defs) push ALL_CONV tm
  in
    SYM th
  end;

val CLEAN1_DEF_CNF_CONV =
  (REWR_CONV EQ_DEFCNF ORELSEC REWR_CONV AND_DEFCNF ORELSEC REWR_CONV OR_DEFCNF)
  THENC REWRITE_CONV [CONJUNCT1 NOT_CLAUSES];

val CLEAN_DEF_CNF_CONV =
  STRIP_EXISTS_CONV
  (CONJUNCTS_CONV (TRY_CONV CLEAN1_DEF_CNF_CONV) THENC
   CONJ_ASSOC_CONV THENC
   CONJUNCTS_CONV DISJ_ASSOC_CONV);

val DEF_CNF_CONV =
  DEF_NNF_CONV THENC PURE_DEF_CNF_CONV THENC CLEAN_DEF_CNF_CONV;

(* ------------------------------------------------------------------------- *)
(* Removes leading existential quantifiers from a theorem.                   *)
(*                                                                           *)
(* Examples:                                                                 *)
(*   EXISTENTIAL_CONST_RULE   ``a``   |- ?x. P x y z                         *)
(*   ---->  [a = @x. P x y z] |- P a y                                       *)
(*                                                                           *)
(*   EXISTENTIAL_CONST_RULE   ``a y z``   |- ?x. P x y                       *)
(*   ---->  [a = \y z. @x. P x y z] |- P (a y z) y                           *)
(*                                                                           *)
(* NEW_CONST_RULE creates a new variable as the argument to                  *)
(* EXISTENTIAL_CONST_RULE, and CLEANUP_CONSTS_RULE tries to eliminate        *)
(* as many of these new equality assumptions as possible.                    *)
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

fun NEW_CONST_RULE th =
  let
    val tm = concl th
    val fvs = free_vars tm
    val (v, _) = dest_exists tm
    val c_type = foldl (fn (h, t) => type_of h --> t) (type_of v) fvs
    val c_vars = list_mk_comb (genvar c_type, rev fvs)
  in
    EXISTENTIAL_CONST_RULE c_vars th
  end;

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
(* Eliminating lambdas to make terms "as first-order as possible".           *)
(*                                                                           *)
(* Example:                                                                  *)
(* ------------------------------------------------------------------------- *)

val LAMB_EQ_ELIM = prove
  (``!(s : 'a -> 'b) t. ((\x. s x) = t) = (!x. s x = t x)``,
   PROVE_TAC []);

val EQ_LAMB_ELIM = prove
  (``!(s : 'a -> 'b) t. (s = (\x. t x)) = (!x. s x = t x)``,
   PROVE_TAC []);

val DELAMB_CONV = SIMP_CONV simplify_ss [EQ_LAMB_ELIM, LAMB_EQ_ELIM];

(* ------------------------------------------------------------------------- *)
(* Eliminating Hilbert's epsilon operator.                                   *)
(*                                                                           *)
(* Example:                                                                  *)
(*                                                                           *)
(*   ((?n. f n = 0) ==> (f n = 0)) ==> 3 < n                                 *)
(*   ---------------------------------------  SELECT_TAC                     *)
(*               3 < @n. f n = 0                                             *)
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
(* Lifting conditionals through function applications.                       *)
(*                                                                           *)
(* Example:  f (if x then 7 else 1)  =  (if x then f 7 else f 1)             *)
(* ------------------------------------------------------------------------- *)

fun cond_lift_rand_CONV tm =
  let
    val (Rator, Rand) = Term.dest_comb tm
    val (f, _) = strip_comb Rator
    val proceed =
      let val {Name,Thy,...} = Term.dest_thy_const f
      in not (Name="COND" andalso Thy="bool")
      end handle HOL_ERR _ => true
  in
    (if proceed then REWR_CONV boolTheory.COND_RAND else NO_CONV) tm
  end;

val cond_lift_SS =
  simpLib.SIMPSET
  {convs =
   [{name = "conditional lifting at rand", trace = 2,
     key = SOME([], Term`(f:'a -> 'b) (COND P Q R)`),
     conv = K (K cond_lift_rand_CONV)}],
   rewrs = [boolTheory.COND_RATOR],
   congs = [],
   filter = NONE,
   ac = [],
   dprocs = []};

val cond_lift_ss = simpLib.++ (pureSimps.pure_ss, cond_lift_SS);

(* ------------------------------------------------------------------------- *)
(* Converting boolean connectives to conditionals.                           *)
(*                                                                           *)
(* Example:  x /\ ~(y ==> ~z)  =  (if x then (if y then z else F) else F)    *)
(* ------------------------------------------------------------------------- *)

val COND_SIMP = prove
  (``!a f g. (if a then f a else g a) = (if a then f T else g F)``,
   RW_TAC boolSimps.bool_ss []);

val COND_NOT = prove
  (``!a. ~a = if a then F else T``,
   RW_TAC boolSimps.bool_ss []
   THEN PROVE_TAC []);

val COND_AND = prove
  (``!a b. a /\ b = (if a then b else F)``,
   RW_TAC boolSimps.bool_ss []
   THEN PROVE_TAC []);

val COND_OR = prove
  (``!a b. a \/ b = if a then T else b``,
   RW_TAC boolSimps.bool_ss []
   THEN PROVE_TAC []);

val COND_IMP = prove
  (``!a b. a ==> b = if a then b else T``,
   RW_TAC boolSimps.bool_ss []
   THEN PROVE_TAC []);

val COND_EQ = prove
  (``!a b. (a = b) = if a then b else ~b``,
   RW_TAC boolSimps.bool_ss []
   THEN PROVE_TAC []);

val COND_COND = prove
  (``!a b c x y.
       (if (if a then b else c) then x else y) =
       (if a then (if b then x else y) else (if c then x else y))``,
   RW_TAC boolSimps.bool_ss []
   THEN PROVE_TAC []);

val COND_ETA = prove
  (``!a. (if a then T else F) = a``,
   RW_TAC boolSimps.bool_ss []);

val COND_SIMP_CONV = CHANGED_CONV (HO_REWR_CONV COND_SIMP);

val condify_SS =
  SIMPSET
  {convs =
   [{name = "COND_SIMP_CONV", trace = 2,
     key = SOME ([], (``if a then b else c``)), conv = K (K COND_SIMP_CONV)}],
   rewrs =
   [COND_CLAUSES, COND_NOT, COND_AND, COND_OR, COND_IMP, COND_EQ, COND_COND,
    COND_ID, COND_ETA, FORALL_SIMP, EXISTS_SIMP],
   congs = [],
   filter = NONE,
   ac = [],
   dprocs = []};

val condify_ss = simpLib.++ (pureSimps.pure_ss, condify_SS);

(* ------------------------------------------------------------------------- *)
(* Evaluating successors of numerals (REDUCE_ss currently doesn't do this).  *)
(*                                                                           *)
(* Examples:  SUC 7 = 8,  SUC 0 = 1                                          *)
(* ------------------------------------------------------------------------- *)

val reduce_suc_SS =
  SIMPSET
  {convs =
   [{name = "evaluating successors of numerals", trace = 2,
     key = SOME([], Term`SUC (NUMERAL n)`), conv = K (K REDUCE_CONV)}],
   rewrs = [GSYM arithmeticTheory.ONE],
   congs = [],
   filter = NONE,
   ac = [],
   dprocs = []};

val reduce_ss =
  simpLib.++
  (simpLib.++ (pureSimps.pure_ss, numSimps.REDUCE_ss), reduce_suc_SS);

(* Quick testing
show_assums := true;
app load ["normalFormsTest"];
open normalFormsTest;

val DEF_CNF_CONV' =
  (time o try)
  (time DEF_NNF_CONV THENC
   time PURE_DEF_CNF_CONV THENC
   time CLEAN_DEF_CNF_CONV);

(* Large formulas *)

val valid1 = time (mk_neg o Term) valid_1;

val _ = DEF_CNF_CONV' valid1;

(* The pigeon-hole principle *)

val test = K () o DEF_CNF_CONV' o time (mk_neg o var_pigeon);

test 8;
test 9;
test 10;
test 11;
test 12;
test 13;
test 14;
test 15;

stop;

READABLE_VARS_CONV (rhs (concl (DEF_CNF_CONV ``~(p = q) ==> q /\ r``)));

try SKI_CONV ``?f. !y. f y = y + 1``;
SKI_CONV ``\x. f x o g``;
SKI_CONV ``\x y. f x y``;
SKI_CONV ``$? = \P. P ($@ P)``;
SKI_CONV ``$==> = \a b. ~a \/ b``;
SKI_CONV ``$! = \P. K T = P``;
SKI_CONV ``!x y. P x y``;
SKI_CONV ``!x y. P y x``;
SKI_CONV ``(P = Q) = (!x. P x = Q x)``;

SIMPLIFY_CONV ``(!x y. P x \/ (P y /\ F)) ==> ?z. P z``;

NNF_CONV ``(!x. P(x)) ==> ((?y. Q(y)) = (?z. P(z) /\ Q(z)))``;
NNF_CONV ``~(~(x = y) = z) = ~(x = ~(y = z))``;

SKOLEMIZE_CONV ``!x. (?y. Q y \/ !z. ~P z \/ ~Q z) \/ ~P x``;

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

try DEF_NNF_CONV ``~(p = ~(q = r)) = ~(~(p = q) = r)``;
try (DEF_CNF_CONV THENC READABLE_VARS_CONV)
``~(p = ~(q = r)) = ~(~(p = q) = r)``;
try PURE_DEF_CNF_CONV ``(p /\ (q \/ r /\ s)) /\ (~p \/ ~q \/ ~s)``;

EXISTENTIAL_CONST_RULE ``a:'a`` (ASSUME ``?x. (P:'a->'b->'c->bool) x y z``);
EXISTENTIAL_CONST_RULE ``(a:'b->'c->'a) y z``
  (ASSUME ``?x. (P:'a->'b->'c->bool) x y z``);
NEW_CONST_RULE (ASSUME ``?x. (P:'a->'b->'c->bool) x y z``);
CLEANUP_CONSTS_RULE it;

DELAMB_CONV ``(\x. f x z) = g z``;

g `3 < @n. f n = 0`;
e SELECT_TAC;
drop ();

g `!p. 0 = @x. (?y w. (@z. z + w = p + q + y + x) = 2) = (?a b. (@c. c + a = p + q + b + x) < 3)`;
e SELECT_TAC;
drop ();

g `(!x. x IN p ==> (f x = f' x)) ==> ((@x. x IN p /\ f x) = @x. x IN p /\ f' x)`;
e STRIP_TAC;
e (CONV_TAC SELECT_NORM_CONV);
e SELECT_TAC;

try (SIMP_CONV cond_lift_ss []) ``f (if x then 7 else 1)``;

try (SIMP_CONV condify_ss []) ``x /\ ~(y ==> ~z)``;

try (SIMP_CONV reduce_ss []) ``SUC 7``;
try (SIMP_CONV reduce_ss []) ``SUC 0``;
*)

(* Expensive tests
val p28 =
  ``(!x. P(x) ==> (!x. Q(x))) /\
    ((!x. Q(x) \/ R(x)) ==> (?x. Q(x) /\ R(x))) /\
    ((?x. R(x)) ==> (!x. L(x) ==> M(x))) ==>
    (!x. P(x) /\ L(x) ==> M(x))``;

time CNF_CONV (mk_neg p28);

val gilmore9 = Term
  `!x. ?y. !z.
     ((!u. ?v. F'(y, u, v) /\ G(y, u) /\ ~H(y, x)) ==>
      (!u. ?v. F'(x, u, v) /\ G(z, u) /\ ~H(x, z)) ==>
      (!u. ?v. F'(x, u, v) /\ G(y, u) /\ ~H(x, y))) /\
     ((!u. ?v. F'(x, u, v) /\ G(y, u) /\ ~H(x, y)) ==>
      ~(!u. ?v. F'(x, u, v) /\ G(z, u) /\ ~H(x, z)) ==>
      (!u. ?v. F'(y, u, v) /\ G(y, u) /\ ~H(y, x)) /\
      (!u. ?v. F'(z, u, v) /\ G(y, u) /\ ~H(z, y)))`;
time CNF_CONV (mk_neg gilmore9);

val p34 =
  ``((?x. !y. P(x) = P(y)) =
     ((?x. Q(x)) = (!y. Q(y)))) =
     ((?x. !y. Q(x) = Q(y)) =
    ((?x. P(x)) = (!y. P(y))))``;

time CNF_CONV (mk_neg p34);

val _ = use "../metis/data/large-problem.sml";
val large_problem = time Term large_problem_frag;
time CNF_CONV (mk_neg large_problem);
*)

end