(* ========================================================================= *)
(* HOL NORMALIZATION FUNCTIONS.                                              *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

(*
app load ["simpLib", "combinTheory", "boolSimps"];
guessing_tyvars := true;
*)

(*
*)
structure normalForms :> normalForms =
struct

open HolKernel Parse boolLib simpLib;

(* Fix the grammar used by this file *)
structure Parse =
struct
  open Parse
  val (Type,Term) = parse_from_grammars combinTheory.combin_grammars
end
open Parse


(* ------------------------------------------------------------------------- *)
(* Tracing.                                                                  *)
(* ------------------------------------------------------------------------- *)

val trace_level = ref 0;
val () = register_trace ("normalForms", trace_level, 10);
fun chatting l = l <= !trace_level;
fun chat s = (Lib.say s; true);

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val ERR = mk_HOL_ERR "normalForms";

fun op_distinct cmp [] = true
  | op_distinct cmp (x :: rest) =
      not (op_mem cmp x rest) andalso op_distinct cmp rest

val beq = ``$= : bool->bool->bool``;

fun dest_beq tm =
  let val (a, b, ty) = dest_eq_ty tm
  in if ty = bool then (a, b) else raise ERR "dest_beq" "not a bool"
  end;

val is_beq = can dest_beq;

fun JUNCTS_CONV p c =
  let fun f t = (if p t then LAND_CONV c THENC RAND_CONV f else c) t in f end;

val CONJUNCTS_CONV = JUNCTS_CONV is_conj;
val DISJUNCTS_CONV = JUNCTS_CONV is_disj;

fun FORALL_CONV c tm =
  if is_forall tm then QUANT_CONV c tm
  else raise ERR "FORALL_CONV" "not a forall";

fun EXISTS_CONV c tm =
  if is_exists tm then QUANT_CONV c tm
  else raise ERR "EXISTS_CONV" "not an exists";

fun STRIP_EXISTS_CONV c tm =
  if is_exists tm then STRIP_QUANT_CONV c tm else c tm;

fun STRIP_FORALL_CONV c tm =
  if is_forall tm then STRIP_QUANT_CONV c tm else c tm;

fun ANTI_ETA_CONV v tm = SYM (ETA_CONV (mk_abs (v, mk_comb (tm, v))));

fun ETA_EXPAND_CONV tm =
  let val (ty,_) = dom_rng (type_of tm) in ANTI_ETA_CONV (genvar ty) tm end;

fun ANTI_BETA_CONV vars tm =
  let
    val tm' = list_mk_comb (list_mk_abs (vars, tm), vars)
    val c = funpow (length vars) (fn c => RATOR_CONV c THENC BETA_CONV) ALL_CONV
  in
    SYM (c tm')
  end;

fun AVOID_SPEC_TAC (tm, v) =
  W (fn (_, g) => SPEC_TAC (tm, variant (free_vars g) v));

local
  open tautLib;
  val th = prove (``(a = b) /\ (c = d) ==> (a /\ c = b /\ d)``, TAUT_TAC);
  val (a, b, c, d) = (``a:bool``, ``b:bool``, ``c:bool``, ``d:bool``);
in
  fun MK_CONJ_EQ th1 th2 =
    let
      val (A, B) = dest_eq (concl th1)
      val (C, D) = dest_eq (concl th2)
    in
      MP (INST [a |-> A, b |-> B, c |-> C, d |-> D] th) (CONJ th1 th2)
    end;
end;

local
  val th = prove (``(a /\ b) /\ c = b /\ (a /\ c)``, tautLib.TAUT_TAC);
  val (a, b, c) = (``a:bool``, ``b:bool``, ``c:bool``);
in
  fun CONJ_RASSOC_CONV tm =
    let
      val (t, C) = dest_conj tm
      val (A, B) = dest_conj t
    in
      INST [a |-> A, b |-> B, c |-> C] th
    end;
end;

local
  val th = prove (``(a \/ b) \/ c = b \/ (a \/ c)``, tautLib.TAUT_TAC);
  val (a, b, c) = (``a:bool``, ``b:bool``, ``c:bool``);
in
  fun DISJ_RASSOC_CONV tm =
    let
      val (t, C) = dest_disj tm
      val (A, B) = dest_disj t
    in
      INST [a |-> A, b |-> B, c |-> C] th
    end;
end;

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
         ren (op_insert aconv v' avoid) dealt
             (INR (sub', b) :: INL (SOME v') :: rest)
       end)
    | ren _ _ _ = raise ERR "prettify_vars" "BUG";
in
  fun prettify_vars tm = ren (all_vars tm) [] [INR ([], tm)];
end;

fun PRETTIFY_VARS_CONV tm =
  ALPHA tm (Lib.with_flag (Globals.priming, SOME "") prettify_vars tm);

(* ------------------------------------------------------------------------- *)
(* Conversion to combinators {S,K,I}.                                        *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (?f. !y. f y = y + 1)                                                   *)
(*   =                                                                       *)
(*   $? (S (K $!) (S (S (K S) (S (K (S (K $=))) I)) (K (S $+ (K 1)))))       *)
(* ------------------------------------------------------------------------- *)

fun COMBIN_CONV ths =
  let
    val mk_combin = FIRST_CONV (map HO_REWR_CONV ths)
    fun conv tm =
      (case dest_term tm of
         CONST _ => ALL_CONV
       | VAR _ => ALL_CONV
       | COMB _ => RATOR_CONV conv THENC RAND_CONV conv
       | LAMB _ => ABS_CONV conv THENC mk_combin THENC conv) tm
  in
    conv
  end;

val MK_S = prove
  (``!x y. (\v. (x v) (y v)) = S (x:'a->'b->'c) y``,
   REPEAT STRIP_TAC THEN
   CONV_TAC (FUN_EQ_CONV) THEN
   SIMP_TAC boolSimps.bool_ss [combinTheory.S_DEF, combinTheory.K_DEF]);

val MK_K = prove
  (``!x. (\v. x) = (K:'a->'b->'a) x``,
   REPEAT STRIP_TAC THEN
   CONV_TAC (FUN_EQ_CONV) THEN
   SIMP_TAC boolSimps.bool_ss [combinTheory.S_DEF, combinTheory.K_DEF]);

val MK_I = prove
  (``(\v. v) = (I:'a->'a)``,
   REPEAT STRIP_TAC THEN
   CONV_TAC (FUN_EQ_CONV) THEN
   SIMP_TAC boolSimps.bool_ss
   [combinTheory.S_DEF, combinTheory.K_DEF, combinTheory.I_THM]);

val SKI_SS =
  simpLib.SSFRAG
  {name=SOME"SKI",
   convs = [], rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};

val SKI_ss = simpLib.++ (pureSimps.pure_ss, SKI_SS);

val SKI_CONV =
  COMBIN_CONV [MK_K, MK_I, MK_S] THENC
  SIMP_CONV SKI_ss [];

(* ------------------------------------------------------------------------- *)
(* Conversion to combinators {S,K,I,C,o}.                                    *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (?f. !y. f y = y + 1)                                                   *)
(*   =                                                                       *)
(*   $? ($! o C (S o $o $= o I) (C $+ 1))                                    *)
(* ------------------------------------------------------------------------- *)

val MK_C = prove
  (``!x y. (\v. (x v) y) = combin$C (x:'a->'b->'c) y``,
   REPEAT STRIP_TAC THEN
   CONV_TAC (FUN_EQ_CONV) THEN
   SIMP_TAC boolSimps.bool_ss
   [combinTheory.S_DEF, combinTheory.K_DEF, combinTheory.C_DEF]);

val MK_o = prove
  (``!x y. (\v:'a. x (y v)) = (x:'b->'c) o y``,
   REPEAT STRIP_TAC THEN
   CONV_TAC (FUN_EQ_CONV) THEN
   SIMP_TAC boolSimps.bool_ss
   [combinTheory.S_DEF, combinTheory.K_DEF, combinTheory.o_DEF]);

val SKICo_SS =
  simpLib.SSFRAG
  {name=SOME"SKICo",
   convs = [], rewrs = [combinTheory.I_o_ID], congs = [],
   filter = NONE, ac = [], dprocs = []};

val SKICo_ss = simpLib.++ (SKI_ss, SKICo_SS);

val SKICo_CONV =
  COMBIN_CONV [MK_K, MK_I, MK_C, MK_o, MK_S] THENC
  SIMP_CONV SKICo_ss [];

(* ------------------------------------------------------------------------- *)
(* Beta reduction and simplifying boolean rewrites.                          *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (!x y. P x \/ (P y /\ F)) ==> ?z. P z                                   *)
(*   =                                                                       *)
(*   (!x. P x) ==> ?z. P z                                                   *)
(* ------------------------------------------------------------------------- *)

val FUN_EQ = prove
  (``!(f : 'a -> 'b) g. (!x. f x = g x) = (f = g)``,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
   REWRITE_TAC []);

val SIMPLIFY_SS =
  simpLib.SSFRAG
  {name=SOME"SIMPLIFY",
   convs = [{name = "extensionality simplification", trace = 2,
             key = SOME([], Term`!x. (f:'a -> 'b) x = g x`),
             conv = K (K (REWR_CONV FUN_EQ))}],
   rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []};

val simplify_ss =
  simpLib.++ (simpLib.++ (pureSimps.pure_ss, boolSimps.BOOL_ss), SIMPLIFY_SS);

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

val NOT_TRUE = prove (``~T = F``, tautLib.TAUT_TAC);

val NOT_FALSE = prove (``~F = T``, tautLib.TAUT_TAC);

val IMP_DISJ_THM' = prove
  (``!x y. x ==> y = y \/ ~x``,
   tautLib.TAUT_TAC);

val NIMP_CONJ_THM = prove
  (``!x y. ~(x ==> y) = x /\ ~y``,
   tautLib.TAUT_TAC);

val EQ_EXPAND' = prove
  (``!x y. (x = y) = (x \/ ~y) /\ (~x \/ y)``,
   tautLib.TAUT_TAC);

val NEQ_EXPAND = prove
  (``!x y. ~(x = y) = (x \/ y) /\ (~x \/ ~y)``,
   tautLib.TAUT_TAC);

val COND_EXPAND' = prove
  (``!c a b. (if c then a else b) = ((~c \/ a) /\ (c \/ b))``,
   tautLib.TAUT_TAC);

val NCOND_EXPAND = prove
  (``!c a b. ~(if c then a else b) = ((~c \/ ~a) /\ (c \/ ~b))``,
   tautLib.TAUT_TAC);

val DE_MORGAN_THM1 = prove
  (``!x y. ~(x /\ y) = (~x \/ ~y)``,
   tautLib.TAUT_TAC);

val DE_MORGAN_THM2 = prove
  (``!x y. ~(x \/ y) = (~x /\ ~y)``,
   tautLib.TAUT_TAC);

val NNF_EXISTS_UNIQUE = prove
  (``!p. $?! p = ((?(x : 'a). p x) /\ !x y. p x /\ p y ==> (x = y))``,
   GEN_TAC THEN
   (KNOW_TAC ``$?! p = ?!(x : 'a). p x`` THEN1
    (CONV_TAC (DEPTH_CONV (ETA_CONV)) THEN REWRITE_TAC [])) THEN
   DISCH_THEN (fn th => REWRITE_TAC [th]) THEN
   REWRITE_TAC [EXISTS_UNIQUE_THM]);

val NOT_EXISTS_UNIQUE = prove
  (``!p. ~($?! p) = ((!(x : 'a). ~p x) \/ ?x y. p x /\ p y /\ ~(x = y))``,
   REWRITE_TAC [NNF_EXISTS_UNIQUE, DE_MORGAN_THM1] THEN
   CONV_TAC (TOP_DEPTH_CONV (NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV)) THEN
   REWRITE_TAC [NOT_IMP, CONJ_ASSOC]);

val RES_FORALL_THM = prove
  (``!p m. RES_FORALL p m = !(x : 'a). x IN p ==> m x``,
   REWRITE_TAC [RES_FORALL_DEF] THEN BETA_TAC THEN REWRITE_TAC []);

val RES_EXISTS_THM = prove
  (``!p m. RES_EXISTS p m = ?(x : 'a). x IN p /\ m x``,
   REWRITE_TAC [RES_EXISTS_DEF] THEN BETA_TAC THEN REWRITE_TAC []);

val NOT_RES_FORALL = prove
  (``!p m. ~RES_FORALL p m = ?(x : 'a). x IN p /\ ~m x``,
   REWRITE_TAC [RES_FORALL_THM] THEN
   CONV_TAC (DEPTH_CONV NOT_FORALL_CONV) THEN
   REWRITE_TAC [IMP_DISJ_THM, DE_MORGAN_THM2]);

val NOT_RES_EXISTS = prove
  (``!p m. ~RES_EXISTS p m = !(x : 'a). x IN p ==> ~m x``,
   REWRITE_TAC [RES_EXISTS_THM] THEN
   CONV_TAC (DEPTH_CONV NOT_EXISTS_CONV) THEN
   REWRITE_TAC [IMP_DISJ_THM, DE_MORGAN_THM2, DE_MORGAN_THM1]);

fun NNF_SUB_CONV c tm =
  (if is_forall tm then QUANT_CONV c
   else if is_exists tm then QUANT_CONV c
   else if is_conj tm then LAND_CONV c THENC RAND_CONV c
   else if is_disj tm then LAND_CONV c THENC RAND_CONV c
   else NO_CONV) tm;

local
  fun NEG_CONV c tm = (if is_neg tm then RAND_CONV c else NO_CONV) tm;
  val beta_neg =
    REWR_CONV (CONJUNCT1 NOT_CLAUSES) ORELSEC
    BETA_CONV ORELSEC NEG_CONV BETA_CONV;
  val push_neg = FIRST_CONV
    (map REWR_CONV
     [NOT_TRUE, NOT_FALSE, IMP_DISJ_THM', NIMP_CONJ_THM, EQ_EXPAND',
      NEQ_EXPAND, COND_EXPAND', NCOND_EXPAND, DE_MORGAN_THM1, DE_MORGAN_THM2,
      NNF_EXISTS_UNIQUE, NOT_EXISTS_UNIQUE,
      RES_FORALL_THM, RES_EXISTS_THM, NOT_RES_FORALL, NOT_RES_EXISTS] @
     [NOT_FORALL_CONV, NOT_EXISTS_CONV]);
  val q_neg = REPEATC beta_neg THENC TRY_CONV push_neg;
in
  fun PARTIAL_NNF_CONV c tm =
    (q_neg THENC
     (NNF_SUB_CONV (PARTIAL_NNF_CONV c) ORELSEC TRY_CONV c)) tm;
end;

fun PURE_NNF_CONV' c tm =
  PARTIAL_NNF_CONV (c THENC PURE_NNF_CONV' c) tm;
val PURE_NNF_CONV = PURE_NNF_CONV' NO_CONV;

fun NNF_CONV' c = SIMPLIFY_CONV THENC PURE_NNF_CONV' c;
val NNF_CONV = NNF_CONV' NO_CONV;

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
(* Prenex Normal Form.                                                       *)
(* ------------------------------------------------------------------------- *)

local
  val r1 = HO_REWR_CONV (GSYM FORALL_AND_THM);
  val r2 = HO_REWR_CONV LEFT_AND_FORALL_THM;
  val r3 = HO_REWR_CONV RIGHT_AND_FORALL_THM;
  val r4 = HO_REWR_CONV (GSYM LEFT_FORALL_OR_THM);
  val r5 = HO_REWR_CONV (GSYM RIGHT_FORALL_OR_THM);

  fun p tm =
    ((r1 ORELSEC r2 ORELSEC r3 ORELSEC r4 ORELSEC r5) THENC
     TRY_CONV (QUANT_CONV p)) tm;
in
  val PRENEX_CONV = DEPTH_CONV p;
end;

local
  val r1 = HO_REWR_CONV (GSYM LEFT_AND_FORALL_THM);
  val r2 = HO_REWR_CONV (GSYM RIGHT_AND_FORALL_THM);
  val r3 = HO_REWR_CONV FORALL_AND_THM;

  fun p tm =
    ((r1 THENC TRY_CONV (LAND_CONV p)) ORELSEC
     (r2 THENC TRY_CONV (RAND_CONV p)) ORELSEC
     r3 THENC BINOP_CONV (TRY_CONV p)) tm;
in
  val ANTI_PRENEX_CONV = DEPTH_CONV p;
end;

(* ------------------------------------------------------------------------- *)
(* A basic tautology prover and simplifier for clauses                       *)
(*                                                                           *)
(* Examples:                                                                 *)
(*   TAUTOLOGY_CONV:   p \/ r \/ ~p \/ ~q   =  T                             *)
(*   CONTRACT_CONV:    (p \/ r) \/ p \/ ~q  =  p \/ r \/ ~q                  *)
(* ------------------------------------------------------------------------- *)

val BOOL_CASES = prove
  (``!a b. (a ==> b) /\ (~a ==> b) ==> b``,
   tautLib.TAUT_TAC);

val T_OR = prove
  (``!t. T \/ t = T``,
   tautLib.TAUT_TAC);

val OR_T = prove
  (``!t. t \/ T = T``,
   tautLib.TAUT_TAC);

val T_AND = prove
  (``!t. T /\ t = t``,
   tautLib.TAUT_TAC);

val AND_T = prove
  (``!t. t /\ T = t``,
   tautLib.TAUT_TAC);

val OR_F = prove
  (``!t. t \/ F = t``,
   tautLib.TAUT_TAC);

val CONTRACT_DISJ = prove
  (``!a b b'. (~a ==> (b = b')) ==> (~a ==> (a \/ b = b'))``,
   tautLib.TAUT_TAC);

val DISJ_CONGRUENCE = prove
  (``!a b b'. (~a ==> (b = b')) ==> (a \/ b = a \/ b')``,
   tautLib.TAUT_TAC);

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
    else if aconv tm d then
      foldl (fn ((true, a), th) => DISJ2 a th | ((false, b), th) => DISJ1 th b)
            (ASSUME d)
            path
    else
      prove_case d rest

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
      case op_intersect aconv (map dest_neg neg) pos of
          [] => NO_CONV tm
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
      val b_th = DISCH a' (if aconv b F then REFL F else contract (a :: asms) b)
    in
      if op_mem aconv a asms then UNDISCH (MATCH_MP CONTRACT_DISJ b_th)
      else CONV_RULE (TRY_CONV (RAND_CONV simplify_or_f))
           (MATCH_MP DISJ_CONGRUENCE b_th)
    end
in
  val CONTRACT_CONV = W
    (fn tm =>
     if op_distinct aconv (disjuncts tm) then NO_CONV
     else DEPTH_CONV DISJ_RASSOC_CONV THENC contract []);
end;

(* ------------------------------------------------------------------------- *)
(* Conjunctive Normal Form.                                                  *)
(*                                                                           *)
(* Example:                                                                  *)
(*  (!x. P x ==> ?y z. Q y \/ ~?z. P z \/ Q z)                               *)
(*  =                                                                        *)
(*  ?y. (!x x'. Q (y x) \/ ~P x' \/ ~P x) /\ !x x'. Q (y x) \/ ~Q x' \/ ~P x *)
(* ------------------------------------------------------------------------- *)

val tautology_checking = ref true;

val TSIMP_CONV =
  REWR_CONV OR_T ORELSEC REWR_CONV T_OR ORELSEC
  REWR_CONV AND_T ORELSEC REWR_CONV T_AND;

local
  val r1 = REWR_CONV LEFT_OR_OVER_AND;
  val r2 = REWR_CONV RIGHT_OR_OVER_AND;
  val p1 = r1 ORELSEC r2;
  val p2 = TAUTOLOGY_CONV ORELSEC CONTRACT_CONV;
  val ps = TRY_CONV TSIMP_CONV;
in
  fun PUSH_ORS_CONV tm =
    (TSIMP_CONV ORELSEC
     (p1 THENC BINOP_CONV (TRY_CONV PUSH_ORS_CONV) THENC ps) ORELSEC
     (if !tautology_checking then p2 else NO_CONV)) tm;
end;

val CLEAN_CNF_CONV =
  DEPTH_CONV (DISJ_RASSOC_CONV ORELSEC CONJ_RASSOC_CONV ORELSEC
              REWR_CONV FORALL_SIMP ORELSEC REWR_CONV EXISTS_SIMP);

val PURE_CNF_CONV =
  STRIP_EXISTS_CONV (STRIP_FORALL_CONV (DEPTH_CONV PUSH_ORS_CONV)) THENC
  CLEAN_CNF_CONV;

fun CNF_CONV' c =
  NNF_CONV' c THENC
  SKOLEMIZE_CONV THENC
  PRENEX_CONV THENC
  PURE_CNF_CONV;

val CNF_CONV = CNF_CONV' NO_CONV;

(* ------------------------------------------------------------------------- *)
(* Disjunctive Normal Form.                                                  *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (!x. P x ==> ?y z. Q y \/ ~?z. P z \/ Q z)                              *)
(*   =                                                                       *)
(*   !x z. (?y. Q y) \/ (?y. ~P (z y) /\ ~Q (z y)) \/ ~P x                   *)
(* ------------------------------------------------------------------------- *)

val DOUBLE_NEG_CONV = REWR_CONV (GSYM (CONJUNCT1 NOT_CLAUSES));

fun NEG_CONV c tm =
  ((if is_neg tm then ALL_CONV else DOUBLE_NEG_CONV) THENC RAND_CONV c) tm;

fun DNF_CONV' c =
  DOUBLE_NEG_CONV THENC RAND_CONV (CNF_CONV' (NEG_CONV c)) THENC PURE_NNF_CONV;

val DNF_CONV = DNF_CONV' NO_CONV;

(* ------------------------------------------------------------------------- *)
(* Definitional Negation Normal Form                                         *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ((p = (q = r)) = ((p = ~q) = ~r))                                       *)
(* ------------------------------------------------------------------------- *)

val NEG_EQ = prove
  (``!a b. ~(a = b) = (a = ~b)``,
   tautLib.TAUT_TAC);

fun DEF_NNF_SUB_CONV c tm =
  (if is_forall tm then QUANT_CONV c
   else if is_exists tm then QUANT_CONV c
   else if is_conj tm then LAND_CONV c THENC RAND_CONV c
   else if is_disj tm then LAND_CONV c THENC RAND_CONV c
   else if is_beq tm then LAND_CONV c THENC RAND_CONV c
   else NO_CONV) tm;

local
  fun NEG_CONV c tm = (if is_neg tm then RAND_CONV c else NO_CONV) tm;
  val beta_neg =
    REWR_CONV (CONJUNCT1 NOT_CLAUSES) ORELSEC
    BETA_CONV ORELSEC NEG_CONV BETA_CONV;
  val push_neg = FIRST_CONV
    (map REWR_CONV
     [NOT_TRUE, NOT_FALSE, IMP_DISJ_THM', NIMP_CONJ_THM, NEG_EQ,
      COND_EXPAND', NCOND_EXPAND, DE_MORGAN_THM1, DE_MORGAN_THM2,
      NNF_EXISTS_UNIQUE, NOT_EXISTS_UNIQUE,
      RES_FORALL_THM, RES_EXISTS_THM, NOT_RES_FORALL, NOT_RES_EXISTS] @
     [NOT_FORALL_CONV, NOT_EXISTS_CONV]);
  val q_neg = REPEATC beta_neg THENC TRY_CONV push_neg;
in
  fun PARTIAL_DEF_NNF_CONV c tm =
    (q_neg THENC
     (DEF_NNF_SUB_CONV (PARTIAL_DEF_NNF_CONV c) ORELSEC TRY_CONV c)) tm;
end;

fun PURE_DEF_NNF_CONV' c tm =
  PARTIAL_DEF_NNF_CONV (c THENC PURE_DEF_NNF_CONV' c) tm;
val PURE_DEF_NNF_CONV = PURE_DEF_NNF_CONV' NO_CONV;

fun DEF_NNF_CONV' c = SIMPLIFY_CONV THENC PURE_DEF_NNF_CONV' c;
val DEF_NNF_CONV = DEF_NNF_CONV' NO_CONV;

datatype nnf_pos = Formula_pos | Atom_pos | Inside_pos;

fun find_nnf find_f =
  let
    val fp = Formula_pos
    fun f [] = raise ERR "find_nnf" ""
      | f (p_vs_tm :: tms) = if find_f p_vs_tm then p_vs_tm else g p_vs_tm tms
    and g (Formula_pos,vs,tm) tms =
      if is_conj tm then
        let val (a,b) = dest_conj tm in f ((fp,vs,a)::(fp,vs,b)::tms) end
      else if is_disj tm then
        let val (a,b) = dest_disj tm in f ((fp,vs,a)::(fp,vs,b)::tms) end
      else if is_beq tm then
        let val (a,b) = dest_beq tm in f ((fp,vs,a)::(fp,vs,b)::tms) end
      else if is_forall tm then
        let val (v,b) = dest_forall tm in f ((fp, v :: vs, b) :: tms) end
      else if is_exists tm then
        let val (v,b) = dest_exists tm in f ((fp, v :: vs, b) :: tms) end
      else if is_neg tm then
        let val a = dest_neg tm in f ((fp, vs, a) :: tms) end
      else f ((Atom_pos, vs, tm) :: tms)
      | g (_,vs,tm) tms =
      if not (is_comb tm) then f tms
      else f ((Inside_pos, vs, rator tm) :: (Inside_pos, vs, rand tm) :: tms)
  in
    fn tm => f [(fp,[],tm)]
  end;

fun ATOM_CONV c tm = (if is_neg tm then RAND_CONV c else c) tm;

(* ------------------------------------------------------------------------- *)
(* Definitional Conjunctive Normal Form                                      *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (~(p = ~(q = r)) = ~(~(p = q) = r))                                     *)
(*   =                                                                       *)
(*   ?v v1 v2 v3 v4.                                                         *)
(*     (v4 \/ v1 \/ v3) /\ (v4 \/ ~v1 \/ ~v3) /\ (v1 \/ ~v3 \/ ~v4) /\       *)
(*     (v3 \/ ~v1 \/ ~v4) /\ (v3 \/ v2 \/ ~r) /\ (v3 \/ ~v2 \/ r) /\         *)
(*     (v2 \/ r \/ ~v3) /\ (~r \/ ~v2 \/ ~v3) /\ (v2 \/ p \/ ~q) /\          *)
(*     (v2 \/ ~p \/ q) /\ (p \/ q \/ ~v2) /\ (~q \/ ~p \/ ~v2) /\            *)
(*     (v1 \/ p \/ v) /\ (v1 \/ ~p \/ ~v) /\ (p \/ ~v \/ ~v1) /\             *)
(*     (v \/ ~p \/ ~v1) /\ (v \/ q \/ r) /\ (v \/ ~q \/ ~r) /\               *)
(*     (q \/ ~r \/ ~v) /\ (r \/ ~q \/ ~v) /\ v4                              *)
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
  case List.find (fn (_, b) => aconv b tm) defs of
      NONE => let val g = genvar bool in ((g, tm) :: defs, g) end
    | SOME (v, _) => (defs, v);

fun gen_cnf defs tm =
  if is_conj tm then
    def_step (sub_cnf gen_cnf conjunction defs (dest_conj tm))
  else if is_disj tm then
    def_step (sub_cnf gen_cnf disjunction defs (dest_disj tm))
  else if is_beq tm then
    def_step (sub_cnf gen_cnf beq defs (dest_beq tm))
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

fun gen_def_cnf tm =
  let
    val (defs, tm) = conj_cnf [] tm
    val (vs, eqs) = unzip (map (fn (v, d) => (v, mk_eq (v, d))) (rev defs))
    val tm = list_mk_exists (vs, foldl mk_conj tm eqs)
  in
    (defs, tm)
  end;

fun PURE_DEF_CNF_CONV tm =
  let
    val (defs, tm) = gen_def_cnf tm
    fun push c = QUANT_CONV c THENC ONE_POINT_CONV
    val th = QCONV (funpow (length defs) push ALL_CONV) tm
  in
    SYM th
  end;

val def_cnf = snd o gen_def_cnf;

val CLEAN_DEF_CNF_CONV =
  (REWR_CONV EQ_DEFCNF ORELSEC
   REWR_CONV AND_DEFCNF ORELSEC
   REWR_CONV OR_DEFCNF)
  THENC REWRITE_CONV [CONJUNCT1 NOT_CLAUSES];

local
  datatype btree = LEAF of term | BRANCH of btree * btree;

  fun btree_fold b f (LEAF tm) = b tm
    | btree_fold b f (BRANCH (s, t)) = f (btree_fold b f s) (btree_fold b f t);

  fun btree_strip_conj tm =
    if is_conj tm then
      (BRANCH o (btree_strip_conj ## btree_strip_conj) o dest_conj) tm
    else LEAF tm;

  val rewr = QCONV (CLEAN_DEF_CNF_CONV ORELSEC DEPTH_CONV DISJ_RASSOC_CONV);

  fun cleanup tm =
    let
      val b = btree_strip_conj tm
      val th = btree_fold rewr MK_CONJ_EQ b
    in
      CONV_RULE (RAND_CONV (DEPTH_CONV CONJ_RASSOC_CONV)) th
    end;
in
  val CLEANUP_DEF_CNF_CONV = STRIP_EXISTS_CONV cleanup;
end;

local
  val without_proof = curry (mk_oracle_thm "Definitional_CNF") [];
in
  fun ORACLE_PURE_DEF_CNF_CONV tm = without_proof (mk_eq (tm, def_cnf tm));
end;

val DEF_CNF_CONV =
  DEF_NNF_CONV THENC PURE_DEF_CNF_CONV THENC CLEANUP_DEF_CNF_CONV;

val ORACLE_DEF_CNF_CONV =
  DEF_NNF_CONV THENC ORACLE_PURE_DEF_CNF_CONV THENC CLEANUP_DEF_CNF_CONV;

(* ------------------------------------------------------------------------- *)
(* Removes leading existential quantifiers from a theorem, by introducing a  *)
(* new skolem constant with an appropriate assumption.                       *)
(*                                                                           *)
(* Examples:                                                                 *)
(*   SKOLEM_CONST_RULE   ``a``   |- ?x. P x y z                              *)
(*   ---->  [a = @x. P x y z] |- P a y                                       *)
(*                                                                           *)
(*   SKOLEM_CONST_RULE   ``a y z``   |- ?x. P x y                            *)
(*   ---->  [a = \y z. @x. P x y z] |- P (a y z) y                           *)
(*                                                                           *)
(* NEW_SKOLEM_CONST generates an argument for SKOLEM_CONST_RULE, and         *)
(* NEW_SKOLEM_CONST_RULE puts the two functions together.                    *)
(* CLEANUP_SKOLEM_CONSTS_RULE tries to eliminate as many 'skolem             *)
(* assumptions' as possible.                                                 *)
(* ------------------------------------------------------------------------- *)

local
  fun comb_beta (x, eq_th) =
    CONV_RULE (RAND_CONV BETA_CONV) (MK_COMB (eq_th, REFL x))
in
  fun SKOLEM_CONST_RULE c_vars th =
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

fun NEW_SKOLEM_CONST th =
  let
    val tm = concl th
    val fvs = op_set_diff aconv (free_vars tm) (free_varsl (hyp th))
    val (v, _) = dest_exists tm
    val c_type = foldl (fn (h, t) => type_of h --> t) (type_of v) fvs
    val c_vars = list_mk_comb (genvar c_type, rev fvs)
  in
    c_vars
  end;

val NEW_SKOLEM_CONST_RULE = W (SKOLEM_CONST_RULE o NEW_SKOLEM_CONST);

local
  fun zap _ _ [] = raise ERR "zap" "fresh out of asms"
    | zap th checked (asm :: rest) =
    if is_eq asm then
      let
        val (v,def) = dest_eq asm
      in
        if is_var v andalso all (not o free_in v) (def :: checked @ rest) then
          MP (SPEC def (GEN v (DISCH asm th))) (REFL def)
        else zap th (asm :: checked) rest
      end
    else zap th (asm :: checked) rest;
in
  val CLEANUP_SKOLEM_CONSTS_RULE = repeat (fn th => zap th [concl th] (hyp th));
end;

(* ------------------------------------------------------------------------- *)
(* Eliminating lambdas to make terms "as first-order as possible".           *)
(*                                                                           *)
(* Example:  ((\x. f x z) = g z)  =  !x. f x z = g z x                       *)
(* ------------------------------------------------------------------------- *)

val LAMB_EQ_ELIM = prove
  (``!(s : 'a -> 'b) t. ((\x. s x) = t) = (!x. s x = t x)``,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
   SIMP_TAC boolSimps.bool_ss []);

val EQ_LAMB_ELIM = prove
  (``!(s : 'a -> 'b) t. (s = (\x. t x)) = (!x. s x = t x)``,
   CONV_TAC (DEPTH_CONV FUN_EQ_CONV) THEN
   SIMP_TAC boolSimps.bool_ss []);

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
  fun norm vars tm =
    let
      val (a,b) = dest_comb tm
      val _ = same_const select a orelse raise ERR "norm" "not a select"
      val conv = ANTI_BETA_CONV (op_intersect aconv (free_vars b) vars)
      val conv =
        if is_abs b then conv else
          let
            val (ty,_) = dom_rng (type_of b)
            val v = variant (all_vars b) (mk_var ("v", ty))
          in
            RAND_CONV (ANTI_ETA_CONV v) THENC conv
          end
    in
      conv tm
    end;

  fun select_norm vars tm =
    let val svars = (case dest_term tm of LAMB (v,_) => v :: vars | _ => vars)
    in SUB_CONV (select_norm svars) THENC TRY_CONV (norm vars)
    end tm;
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

local
  fun get vs tm =
    case
      (case dest_term tm of COMB (x, y) =>
         (case get vs x of s as SOME _ => s | NONE => get vs y)
       | LAMB (v, b) => get (v :: vs) b
       | _ => NONE) of s as SOME _ => s
       | NONE =>
         if is_select (snd (strip_abs tm)) andalso
           null (op_intersect aconv (free_vars tm) vs)
         then SOME tm
         else NONE;
in
  val get_vselect = partial (ERR "get_vselect" "not found") (get []);
end;

val SPEC_ONE_SELECT_TAC = W (fn (_, tm) => SPEC_VSELECT_TAC (get_vselect tm));

val SELECT_TAC = CONV_TAC SELECT_NORM_CONV THEN REPEAT SPEC_ONE_SELECT_TAC;

(* ------------------------------------------------------------------------- *)
(* Remove all Abbrev terms from a goal by rewriting them away (Abbrev = I)   *)
(* ------------------------------------------------------------------------- *)

val REMOVE_ABBR_TAC =
    PURE_REWRITE_TAC [markerTheory.Abbrev_def] THEN
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [markerTheory.Abbrev_def]);

(* ------------------------------------------------------------------------- *)
(* Lifting conditionals through function applications.                       *)
(*                                                                           *)
(* Example:  f (if x then y else z)  =  (if x then f y else f z)             *)
(* ------------------------------------------------------------------------- *)

fun cond_lift_rand_CONV tm =
  let
    val (Rator,Rand) = Term.dest_comb tm
    val (f,_) = strip_comb Rator
    val proceed =
      let val {Name,Thy,...} = Term.dest_thy_const f
      in not (Name="COND" andalso Thy="bool")
      end handle HOL_ERR _ => true
  in
    (if proceed then REWR_CONV boolTheory.COND_RAND else NO_CONV) tm
  end;

val cond_lift_SS =
  simpLib.SSFRAG
  {name=SOME"cond_lift",
   convs =
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
  (``!a f g. (if a then f a else g a):'a = (if a then f T else g F)``,
   SIMP_TAC boolSimps.bool_ss []);

val COND_NOT = prove
  (``!a. ~a = if a then F else T``,
   SIMP_TAC boolSimps.bool_ss []);

val COND_AND = prove
  (``!a b. a /\ b = (if a then b else F)``,
   SIMP_TAC boolSimps.bool_ss []);

val COND_OR = prove
  (``!a b. a \/ b = if a then T else b``,
   SIMP_TAC boolSimps.bool_ss []);

val COND_IMP = prove
  (``!a b. a ==> b = if a then b else T``,
   SIMP_TAC boolSimps.bool_ss []);

val COND_EQ = prove
  (``!a b. (a = b) = if a then b else ~b``,
   SIMP_TAC boolSimps.bool_ss [EQ_IMP_THM, COND_EXPAND]
   THEN tautLib.TAUT_TAC);

val COND_COND = prove
  (``!a b c x y.
       (if (if a then b else c) then (x:'a) else y) =
       (if a then (if b then x else y) else (if c then x else y))``,
   STRIP_TAC
   THEN MP_TAC (SPEC ``a:bool`` EXCLUDED_MIDDLE)
   THEN STRIP_TAC
   THEN ASM_SIMP_TAC boolSimps.bool_ss []);

val COND_ETA = prove
  (``!a. (if a then T else F) = a``,
   SIMP_TAC boolSimps.bool_ss []);

val COND_SIMP_CONV = CHANGED_CONV (HO_REWR_CONV COND_SIMP);

val condify_SS =
  SSFRAG
  {name=SOME"condify",
   convs =
   [{name = "COND_SIMP_CONV", trace = 2,
     key = SOME ([], (``if a then (b:'a) else c``)),
     conv = K (K COND_SIMP_CONV)}],
   rewrs =
   [COND_CLAUSES, COND_NOT, COND_AND, COND_OR, COND_IMP, COND_EQ, COND_COND,
    COND_ID, COND_ETA, FORALL_SIMP, EXISTS_SIMP],
   congs = [],
   filter = NONE,
   ac = [],
   dprocs = []};

val condify_ss = simpLib.++ (pureSimps.pure_ss, condify_SS);

(* ------------------------------------------------------------------------- *)
(* Definitional CNF minimizing number of clauses.                            *)
(*                                                                           *)
(* Example:                                                                  *)
(* |- (p /\ q /\ r) \/ (s /\ t /\ u)                                         *)
(*    -->                                                                    *)
(* ([``d``],                                                                 *)
(*   [[.] |- (d \/ s) /\ (d \/ t) /\ (d \/ u),                               *)
(*    [.] |- (d \/ ~p \/ ~q \/ ~r) /\ (~d \/ p) /\ (~d \/ q) /\ (~d \/ r)])  *)
(*                                                                           *)
(* where the assumption [.] in both theorems is d = (p /\ q /\ r).           *)
(* ------------------------------------------------------------------------- *)

val COND_BOOL = prove
  (``!c. (if c then T else F) = c``,
   tautLib.TAUT_TAC);

local
  fun comb_beta (x,eq_th) =
    CONV_RULE (RAND_CONV BETA_CONV) (MK_COMB (eq_th, REFL x));

  fun mk_def defs vs tm =
    let
      val def_tm = list_mk_abs (vs,tm)
    in
      case List.find (aconv def_tm o fst) defs of
        SOME (_,(vs,tm,def)) =>
        let
          val _ = chatting 2 andalso chat "min_cnf: reusing definition.\n"
        in
          (defs, vs, tm, def, NONE)
        end
      | NONE =>
        let
          val c = genvar (type_of def_tm)
          val def0 = foldl comb_beta (ASSUME (mk_eq (c,def_tm))) vs
          val def = SYM def0
          val def_th = GENL vs def0
          val defs = (def_tm,(vs,tm,def)) :: defs
        in
          (defs, vs, tm, def, SOME def_th)
        end
    end;

  fun check_sub vs {redex,residue} =
    op_mem aconv redex vs andalso (type_of redex <> bool orelse is_var residue);

  fun match_convish vs tm def tm' =
    let
      val (tmS,tyS) = match_term tm tm'
      val _ = null tyS orelse raise ERR "rename" "type match"
      val _ = all (check_sub vs) tmS orelse raise ERR "rename" "term match"
    in
      INST tmS def
    end;
in
  fun rename defs vs tm =
    let
      val vs = filter (fn v => op_mem aconv v vs) (free_vars tm)
      val (defs,vs,tm,def,def_th) = mk_def defs vs tm
      val convish = match_convish vs tm def
    in
      (defs, CONV_RULE (TOP_DEPTH_CONV convish), def_th)
    end
    handle e as HOL_ERR _
      => (chat "normalForms.rename should never fail"; Raise e);
end;

(*
local
  fun is_a_bool (p,vs,tm) =
    p = Inside_pos andalso
    type_of tm = bool andalso
    tm <> T andalso tm <> F andalso
    not let val (t,ws) = strip_comb tm in is_var t andalso subset ws vs end;
in
  fun extract_bools (defs,th,acc) =
    let
      val (_,vs,tm) = find_nnf is_a_bool (concl th)
      val (defs,rule,vth) = rename defs vs tm
      val acc = case vth of SOME vt => vt :: acc | NONE => acc
    in
      (defs, rule th, acc)
    end;
end;

fun extract_lambdas (defs,th,acc) =
  let
    val (_,vs,tm) = find_nnf (is_abs o #3) (concl th)
    val (defs,rule,vth) = rename defs vs tm
    val acc = case vth of SOME vt => vt :: acc | NONE => acc
  in
    (defs, rule th, acc)
  end;
*)

local
  val condify_bool = REWR_CONV (GSYM COND_BOOL);

  val let_conv = REWR_CONV LET_THM;

  fun is_a_bool tm =
    type_of tm = bool andalso not (aconv tm T) andalso not (aconv tm F);

  fun lift_cond tm =
    TRY_CONV
    (REPEATC let_conv
     THENC COMB_CONV lift_bool
     THENC (REWR_CONV COND_RATOR
            ORELSEC REWR_CONV COND_RAND
            ORELSEC ALL_CONV)) tm
  and lift_bool tm =
    (chatting 3 andalso chat ("lift_bool: tm = " ^ term_to_string tm ^ "\n");
     (if is_cond tm then ALL_CONV
(* Can't do this without more proof support for booleans
      else if is_a_bool tm then condify_bool
*)
      else lift_cond) tm);
in
  val boolify_conv = ATOM_CONV (CHANGED_CONV lift_cond);
end;

fun min_cnf_prep defs acc [] = (defs, rev acc)
  | min_cnf_prep defs acc (th :: ths) =
  let
    val th = CONV_RULE DELAMB_CONV th
    val th = CONV_RULE (DEF_NNF_CONV' boolify_conv) th
(*
    val (defs,th,bs) = repeat extract_bools (defs,th,[])
    val (defs,th,ls) = repeat extract_lambdas (defs,th,[])
*)
  in
    min_cnf_prep defs (th :: acc) ths
  end;

local
  open Arbint (* hope that on Poly/ML we can eventually just make
                 Arbint a reference to its built-in infinite int type *)

in

datatype formula = Formula of (int * int) * term list * term * skeleton
and skeleton =
    Conj of formula * formula
  | Disj of formula * formula
  | Beq of formula * formula
  | Lit;

fun conj_count (ap,an) (bp,bn) = (ap + bp, an * bn);
fun disj_count (ap,an) (bp,bn) = (ap * bp, an + bn);
fun beq_count (ap,an) (bp,bn) = (ap * bn + an * bp, ap * bp + an * bn);

fun count_cnf vs tm =
  if is_exists tm then
    let
      val (v,b) = dest_exists tm
    in
      count_cnf (v :: vs) b
    end
  else if is_forall tm then
    let
      val (v,b) = dest_forall tm
    in
      count_cnf (v :: vs) b
    end
  else if is_conj tm then
    let
      val (a,b) = dest_conj tm
      val af as Formula (ac,_,_,_) = count_cnf vs a
      val bf as Formula (bc,_,_,_) = count_cnf vs b
    in
      Formula (conj_count ac bc, vs, tm, Conj (af,bf))
    end
  else if is_disj tm then
    let
      val (a,b) = dest_disj tm
      val af as Formula (ac,_,_,_) = count_cnf vs a
      val bf as Formula (bc,_,_,_) = count_cnf vs b
    in
      Formula (disj_count ac bc, vs, tm, Disj (af,bf))
    end
  else if is_beq tm then
    let
      val (a,b) = dest_beq tm
      val af as Formula (ac,_,_,_) = count_cnf vs a
      val bf as Formula (bc,_,_,_) = count_cnf vs b
    in
      Formula (beq_count ac bc, vs, tm, Beq (af,bf))
    end
  else Formula ((Arbint.one,Arbint.one),vs,tm,Lit);


local
  fun check best [] = best
    | check best ((f, form) :: rest) =
    let
      val (n,_,_) = best
      val Formula ((pos,neg), vs, tm, skel) = form
      val m = f (Arbint.one,Arbint.one) + pos + neg
      val best = if m < n then (m,vs,tm) else best
    in
      break best f skel rest
    end
  and break best f (Conj (a,b)) rest =
    let
      val Formula (ac,_,_,_) = a
      val Formula (bc,_,_,_) = b
      fun fa ac = f (conj_count ac bc)
      fun fb bc = f (conj_count ac bc)
      val rest = (fa,a) :: (fb,b) :: rest
    in
      check best rest
    end
    | break best f (Disj (a,b)) rest =
    let
      val Formula (ac,_,_,_) = a
      val Formula (bc,_,_,_) = b
      fun fa ac = f (disj_count ac bc)
      fun fb bc = f (disj_count ac bc)
      val rest = (fa,a) :: (fb,b) :: rest
    in
      check best rest
    end
    | break best f (Beq (a,b)) rest =
    let
      val Formula (ac,_,_,_) = a
      val Formula (bc,_,_,_) = b
      fun fa ac = f (beq_count ac bc)
      fun fb bc = f (beq_count ac bc)
      val rest = (fa,a) :: (fb,b) :: rest
    in
      check best rest
    end
    | break best _ Lit rest = check best rest;
in
  val min_cnf_search = check;
end;

val simple_cnf_rule = CONV_RULE (CNF_CONV' (CHANGED_CONV SKICo_CONV));

fun min_cnf_norm defs acc [] = (defs, rev acc)
  | min_cnf_norm defs acc (th :: ths) =
  let
    val concl_th = concl th
    val form as Formula ((m,_),_,_,_) = count_cnf [] concl_th
    val (n,vs,tm) = min_cnf_search (m,[],concl_th) [(fst,form)]
  in
    if n < m then
      let
        val _ =
          chatting 1 andalso
          chat ("min_cnf: "^Arbint.toString m^" -> "^
                Arbint.toString n^" clauses\n")
        val _ =
          chatting 2 andalso
          chat ("min_cnf: renaming\n" ^ term_to_string tm ^ "\n")
        val (defs,rule,dth) = rename defs vs tm
        val ths = case dth of SOME dt => dt :: ths | NONE => ths
      in
        min_cnf_norm defs acc (rule th :: ths)
      end
    else
      min_cnf_norm defs (simple_cnf_rule th :: acc) ths
  end;
end (* of local enclosing open Arbint *)

fun MIN_CNF ths =
  let
    val ths = map GEN_ALL ths
    val defs = []
    val (defs,ths) = min_cnf_prep defs [] ths
    val (defs,ths) = min_cnf_norm defs [] ths
    val cs = map (lhs o hd o hyp o #3 o snd) defs
  in
    (cs,ths)
  end;

(* Quick testing
val Term = Parse.Term;
val Type = Parse.Type;
(*show_assums := true;*)
Globals.guessing_tyvars := true;
Globals.priming := SOME "";
app load ["numLib", "arithmeticTheory", "pred_setTheory", "bossLib"];
quietdec := true;
open numLib arithmeticTheory pred_setTheory bossLib;
quietdec := false;
Parse.reveal "C";

(*
PRETTIFY_VARS_CONV (rhs (concl (DEF_CNF_CONV ``~(p = q) ==> q /\ r``)));

try SKI_CONV ``?f. !y. f y = y + 1``;
try SKI_CONV ``\x. f x o g``;
SKI_CONV ``\x y. f x y``;
SKI_CONV ``$? = \P. P ($@ P)``;
SKI_CONV ``$==> = \a b. ~a \/ b``;
SKI_CONV ``$! = \P. K T = P``;
SKI_CONV ``!x y. P x y``;
SKI_CONV ``!x y. P y x``;
SKI_CONV ``(P = Q) = (!x. P x = Q x)``;

try SKICo_CONV ``?f. !y. f y = y + 1``;
try SKICo_CONV ``\x. f x o g``;
SKICo_CONV ``\x y. f x y``;
SKICo_CONV ``$? = \P. P ($@ P)``;
SKICo_CONV ``$==> = \a b. ~a \/ b``;
SKICo_CONV ``$! = \P. K T = P``;
SKICo_CONV ``!x y. P x y``;
SKICo_CONV ``!x y. P y x``;
SKICo_CONV ``(P = Q) = (!x. P x = Q x)``;

SIMPLIFY_CONV ``(!x y. P x \/ (P y /\ F)) ==> ?z. P z``;

try NNF_CONV ``(!x. P(x)) ==> ((?y. Q(y)) = (?z. P(z) /\ Q(z)))``;
NNF_CONV ``~(~(x = y) = z) = ~(x = ~(y = z))``;
val tm = ``~(0 <= m ==>
             0 <= n ==>
             0 < m /\ 0 < n ==>
             ((~(n <= 1) \/ (m = 1)) /\
              (n <= 1 \/ (m + 1 = 1 + n) \/ m <= 0 /\ 1 + n <= 1) \/
              m <= 1 /\ n <= 1 + 0 =
              (m = n)))``;
PARTIAL_NNF_CONV (REWR_CONV NOT_NUM_EQ) tm;
PURE_NNF_CONV' (REWR_CONV NOT_NUM_EQ) tm;

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

val th = DNF_CONV' (REWR_CONV NOT_NUM_EQ)
    ``~(0 <= m ==>
        0 <= n ==>
        0 < m /\ 0 < n ==>
        ((~(n <= 1) \/ (m = 1)) /\
         (n <= 1 \/ (m + 1 = 1 + n) \/ m <= 0 /\ 1 + n <= 1) \/
         m <= 1 /\ n <= 1 + 0 =
         (m = n)))``;
val ds = length (strip_disj (rhs (concl th)));

try DEF_NNF_CONV ``~(p = ~(q = r)) = ~(~(p = q) = r)``;
try (DEF_CNF_CONV THENC PRETTIFY_VARS_CONV)
``~(p = ~(q = r)) = ~(~(p = q) = r)``;
CLEANUP_DEF_CNF_CONV ``?v. (v 0 = (x /\ y) /\ (v 1 = (v 0 = x))) /\ v 0``;
try PURE_DEF_CNF_CONV ``(p /\ (q \/ r /\ s)) /\ (~p \/ ~q \/ ~s)``;

SKOLEM_CONST_RULE ``a:'a`` (ASSUME ``?x. (P:'a->'b->'c->bool) x y z``);
SKOLEM_CONST_RULE ``(a:'b->'c->'a) y z``
  (ASSUME ``?x. (P:'a->'b->'c->bool) x y z``);
NEW_SKOLEM_CONST_RULE (ASSUME ``?x. (P:'a->'b->'c->bool) x y z``);
CLEANUP_SKOLEM_CONSTS_RULE it;

DELAMB_CONV ``(\x. f x z) = g z``;

g `3 < @n. f n = 0`;
e SELECT_TAC;
drop ();

g `!p. 0 = @x. (?y w. (@z. z + w = p + q + y + x) = 2) = (?a b. (@c. c + a = p + q + b + x) < 3)`;
e SELECT_TAC;
drop ();

g `!p. 0 = @x. (?y v. (@(z,r). z + v + r = p + q + y + x) = (2,3)) = (?a b. (@c. c + a = p + q + b + x) < 3)`;
e SELECT_TAC;
drop ();

g `(!x. x IN p ==> (f x = f' x)) ==> ((@x. x IN p /\ f x) = @x. x IN p /\ f' x)`;
e STRIP_TAC;
e SELECT_TAC;
drop ();

g `($@ p) = 3`;
e SELECT_TAC;
drop ();

try (SIMP_CONV cond_lift_ss []) ``f (if x then 7 else 1)``;

try (SIMP_CONV condify_ss []) ``x /\ ~(y ==> ~z)``;
*)

(MIN_CNF o map ASSUME)
[``!b. ~(p (c:bool) (b:bool))``];

(MIN_CNF o map ASSUME)
[``!t. ~(p = f (if x then y else z) (if a then b else c)
        (\q. r (if s then t else u)))``];

(MIN_CNF o map ASSUME)
[``!x. p (\y. y + x)``, ``!z. q (\y. y + z)``];

(MIN_CNF o map ASSUME) [``!q. ~(p /\ f (q /\ r))``];

MIN_CNF [GSPECIFICATION,
         ASSUME ``!x. x IN {y + 1 | y < n \/ y < m} ==> x <= m + n``];

val p34 = mk_neg
  ``((?x. !y. (p : 'a -> bool) x = p y) = ((?x. q x) = !y. q y)) =
    ((?x. !y. q x = q y) = ((?x. p x) = !y. p y))``;

CNF_CONV p34;
MIN_CNF [ASSUME p34];

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

(* Large formulas *)
load "UNLINK";
quietdec := true;
open UNLINK;
quietdec := false;

val DEF_CNF_CONV' =
  time DEF_NNF_CONV THENC
  time PURE_DEF_CNF_CONV THENC
  time CLEANUP_DEF_CNF_CONV;

val _ = time CLEANUP_DEF_CNF_CONV tm2;

val valid1 = time (mk_neg o Term) valid_1;

val _ = time DEF_CNF_CONV' valid1;

(* The pigeon-hole principle *)

fun test n = ((time DEF_CNF_CONV' o time (mk_neg o var_pigeon)) n; n);

test 8;
test 9;
test 10;
test 11;
test 12;
test 13;
test 14;
test 15;

val _ = use "../metis/data/large-problem.sml";
val large_problem = time Term large_problem_frag;
time CNF_CONV (mk_neg large_problem);
*)
*)


end
