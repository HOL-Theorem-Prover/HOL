(* ========================================================================= *)
(* HOL NORMALIZATION FUNCTIONS.                                              *)
(* Created by Joe Hurd, October 2001                                         *)
(* ========================================================================= *)

(*
app load ["simpLib", "combinTheory", "boolSimps"];
guessing_tyvars := false;
*)

(*
*)
structure normalForms :> normalForms =
struct

open HolKernel Parse boolLib simpLib;

infix THEN THENC ORELSEC ++ --> |-> THENQC ORELSEQC ##;

val (Type,Term) = Parse.parse_from_grammars combinTheory.combin_grammars;
val op THENQC = op THENC;
val op ORELSEQC = op ORELSEC;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

val ERR = mk_HOL_ERR "normalForms";

fun distinct [] = true
  | distinct (x :: rest) = not (mem x rest) andalso distinct rest;

val beq = ``$= : bool->bool->bool``;

fun dest_beq tm =
  let val (a, b, ty) = dest_eq_ty tm
  in if ty = bool then (a, b) else raise ERR "dest_beq" "not a bool"
  end;

val is_beq = can dest_beq;

fun MK_QCONV c tm =
  let val th = c tm
  in if rhs (concl th) = tm then raise Conv.UNCHANGED else th
  end;

fun FIRST_QCONV [] _ = raise ERR "FIRST_QCONV" "out of QCONVs"
  | FIRST_QCONV (qc :: rest) tm = (qc ORELSEQC FIRST_QCONV rest) tm;

fun JUNCTS_QCONV p c =
  let fun f t = (if p t then LAND_CONV c THENQC RAND_CONV f else c) t in f end;

val CONJUNCTS_QCONV = JUNCTS_QCONV is_conj;
val DISJUNCTS_QCONV = JUNCTS_QCONV is_disj;

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
         ren (insert v' avoid) dealt (INR (sub', b) :: INL (SOME v') :: rest)
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

val SKI_CONV = COMBIN_CONV [MK_K, MK_I, MK_S];

(* ------------------------------------------------------------------------- *)
(* Conversion to combinators {S,K,I,C,o}.                                    *)
(*                                                                           *)
(* Example:                                                                  *)
(*   (?f. !y. f y = y + 1)                                                   *)
(*   =                                                                       *)
(*   $? ($! o C (S o $o $= o I) (C $+ 1))                                    *)
(* ------------------------------------------------------------------------- *)

val MK_C = prove
  (``!x y. (\v. (x v) y) = C (x:'a->'b->'c) y``,
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

val SKICo_CONV = COMBIN_CONV [MK_K, MK_I, MK_C, MK_o, MK_S];

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
  simpLib.SIMPSET
  {convs = [{name = "extensionality simplification", trace = 2,
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

fun NNF_SUB_QCONV qc tm =
  (if is_forall tm then QUANT_CONV qc
   else if is_exists tm then QUANT_CONV qc
   else if is_conj tm then LAND_CONV qc THENQC RAND_CONV qc
   else if is_disj tm then LAND_CONV qc THENQC RAND_CONV qc
   else NO_CONV) tm;

local
  fun NEG_CONV c tm = (if is_neg tm then RAND_CONV c else NO_CONV) tm;
  val beta_neg =
    REWR_CONV (CONJUNCT1 NOT_CLAUSES) ORELSEC
    BETA_CONV ORELSEC NEG_CONV BETA_CONV;
  val push_neg = FIRST_CONV
    (map REWR_CONV
     [IMP_DISJ_THM', NIMP_CONJ_THM, EQ_EXPAND', NEQ_EXPAND,
      COND_EXPAND', NCOND_EXPAND, DE_MORGAN_THM1, DE_MORGAN_THM2,
      NNF_EXISTS_UNIQUE, NOT_EXISTS_UNIQUE,
      RES_FORALL_THM, RES_EXISTS_THM, NOT_RES_FORALL, NOT_RES_EXISTS] @
     [NOT_FORALL_CONV, NOT_EXISTS_CONV]);
  val q_neg = REPEATC (MK_QCONV beta_neg) THENQC TRY_CONV (MK_QCONV push_neg);
in
  fun PARTIAL_NNF_QCONV qc tm =
    (q_neg THENQC
     (NNF_SUB_QCONV (PARTIAL_NNF_QCONV qc) ORELSEQC TRY_CONV qc)) tm;
end;

fun PURE_NNF_QCONV' qc tm =
  PARTIAL_NNF_QCONV (qc THENQC PURE_NNF_QCONV' qc) tm;
val PURE_NNF_QCONV = PURE_NNF_QCONV' NO_CONV;

fun PURE_NNF_CONV' qc = QCONV (PURE_NNF_QCONV' (MK_QCONV qc));
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

val FORALL_T = prove
  (``(!x:'a. T) = T``,
   ACCEPT_TAC (ISPEC T FORALL_SIMP));

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
     else QCONV (DEPTH_CONV DISJ_RASSOC_CONV THENQC MK_QCONV (contract [])))
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

val CLEAN_CNF_QCONV =
  STRIP_EXISTS_CONV
  (DEPTH_CONV CONJ_RASSOC_CONV THENQC
   CONJUNCTS_QCONV
   (STRIP_FORALL_CONV
    (DEPTH_CONV DISJ_RASSOC_CONV THENQC
     DISJUNCTS_QCONV (MK_QCONV SKICo_CONV))));

val CLEAN_CNF_CONV = QCONV CLEAN_CNF_QCONV;

val PURE_CNF_CONV =
  STRIP_EXISTS_CONV (DEPTH_CONV PUSH_ORS_CONV) THENC CLEAN_CNF_CONV;

fun CNF_CONV' c = NNF_CONV' c THENC SKOLEMIZE_CONV THENC PURE_CNF_CONV;

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

val PURE_DEF_NNF_CONV =
  SIMP_CONV simplify_ss
  [IMP_DISJ_THM, NEG_EQ, hd (CONJUNCTS NOT_CLAUSES), NOT_FORALL_THM,
   NOT_EXISTS_THM, DE_MORGAN_THM];

val DEF_NNF_CONV = SIMPLIFY_CONV THENC PURE_DEF_NNF_CONV;

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
  case List.find (fn (_, b) => b = tm) defs of NONE
    => let val g = genvar bool in ((g, tm) :: defs, g) end
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
    val th = funpow (length defs) push ALL_CONV tm
  in
    SYM th
  end;

val def_cnf = snd o gen_def_cnf;

val CLEAN_DEF_CNF_QCONV =
  (REWR_CONV EQ_DEFCNF ORELSEQC
   REWR_CONV AND_DEFCNF ORELSEQC
   REWR_CONV OR_DEFCNF)
  THENQC MK_QCONV (REWRITE_CONV [CONJUNCT1 NOT_CLAUSES]);

local
  datatype btree = LEAF of term | BRANCH of btree * btree;

  fun btree_fold b f (LEAF tm) = b tm
    | btree_fold b f (BRANCH (s, t)) = f (btree_fold b f s) (btree_fold b f t);

  fun btree_strip_conj tm =
    if is_conj tm then
      (BRANCH o (btree_strip_conj ## btree_strip_conj) o dest_conj) tm
    else LEAF tm;

  val rewr = QCONV (CLEAN_DEF_CNF_QCONV ORELSEQC DEPTH_CONV DISJ_RASSOC_CONV);

  fun cleanup tm =
    let
      val b = btree_strip_conj tm
      val th = btree_fold rewr MK_CONJ_EQ b
    in
      CONV_RULE (RAND_CONV (QCONV (DEPTH_CONV CONJ_RASSOC_CONV))) th
    end;
in
  val CLEANUP_DEF_CNF_CONV = STRIP_EXISTS_CONV cleanup;
end;

local
  val without_proof = curry (mk_oracle_thm (Tag.read "Definitional_CNF")) [];
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
    val fvs = subtract (free_vars tm) (free_varsl (hyp th))
    val (v, _) = dest_exists tm
    val c_type = foldl (fn (h, t) => type_of h --> t) (type_of v) fvs
    val c_vars = list_mk_comb (genvar c_type, rev fvs)
  in
    c_vars
  end;

val NEW_SKOLEM_CONST_RULE = W (SKOLEM_CONST_RULE o NEW_SKOLEM_CONST);

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
    else zap th (asm::checked) rest;
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
(* Example:  f (if x then y else z)  =  (if x then f y else f z)             *)
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
  SIMPSET
  {convs =
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

(* Quick testing
val Term = Parse.Term;
val Type = Parse.Type;
show_assums := true;
Globals.guessing_tyvars := true;
app load ["UNLINK", "numLib", "arithmeticTheory", "bossLib"];
open UNLINK numLib arithmeticTheory bossLib;
Parse.reveal "C";

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
PARTIAL_NNF_QCONV (MK_QCONV (REWR_CONV NOT_NUM_EQ)) tm;
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
CNF_CONV ``?x y. x + y = 2``;

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

g `(!x. x IN p ==> (f x = f' x)) ==> ((@x. x IN p /\ f x) = @x. x IN p /\ f' x)`;
e STRIP_TAC;
e (CONV_TAC SELECT_NORM_CONV);
e SELECT_TAC;
drop ();

try (SIMP_CONV cond_lift_ss []) ``f (if x then 7 else 1)``;

try (SIMP_CONV condify_ss []) ``x /\ ~(y ==> ~z)``;

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