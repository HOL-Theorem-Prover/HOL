structure boolSimps :> boolSimps =
struct

open HolKernel boolLib liteLib simpLib pureSimps
     Ho_Rewrite tautLib Parse;

infix THENQC

(* Fix the grammar used by this file *)
val ambient_grammars = Parse.current_grammars();
val _ = Parse.temp_set_grammars combinTheory.combin_grammars

fun BETA_CONVS tm = (RATOR_CONV BETA_CONVS THENQC BETA_CONV) tm

(* ----------------------------------------------------------------------
    ETA_ss
      Implemented in a slightly cack-handed way so as to avoid simplifying
      things like `!x. P x` to `$! P`
   ---------------------------------------------------------------------- *)

fun comb_ETA_CONV t =
    (if not (is_exists t orelse is_forall t orelse is_select t)
       then RAND_CONV ETA_CONV
       else NO_CONV) t

val ETA_ss = SSFRAG {name = SOME "ETA",
  convs = [{name = "ETA_CONV (eta reduction)",
            trace = 2,
            key = SOME ([],``(f:('a->'b)->'c) (\x:'a. (g:'a->'b) x)``),
            conv = K (K comb_ETA_CONV)},
           {name = "ETA_CONV (eta reduction)",
            trace = 2,
            key = SOME ([], ``\x:'a. \y:'b. (f:'a->'b->'c) x y``),
            conv = K (K (ABS_CONV ETA_CONV))}],
  rewrs = [], congs = [], filter = NONE, ac = [], dprocs = []}

(* ----------------------------------------------------------------------
    literal_case_ss
   ---------------------------------------------------------------------- *)

 val literal_cong = prove(
   ``(v:'a = v') ==> (literal_case (f:'a -> 'b) v = literal_case f (I v'))``,
   DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC [literal_case_THM, combinTheory.I_THM])

val literal_I_thm = prove(
  ``literal_case (f : 'a -> 'b) (I x) = f x``,
  REWRITE_TAC [combinTheory.I_THM, literal_case_THM]);

val literal_case_ss =
    simpLib.SSFRAG
    {name = SOME"literal_case",
     ac = [], congs = [literal_cong], convs = [], filter = NONE,
     dprocs = [], rewrs = [literal_I_thm]}

(* ----------------------------------------------------------------------
    BOOL_ss
      This simpset fragment contains "standard" rewrites, as per the
      default behaviour of REWRITE_TAC.  It also includes
      beta-conversion.
   ---------------------------------------------------------------------- *)


val BOOL_ss = SSFRAG
  {name = SOME"BOOL",
   convs=[{name="BETA_CONV (beta reduction)",
           trace=2,
           key=SOME ([],``(\x:'a. y:'b) z``),
	   conv=K (K BETA_CONV)}],
   rewrs=[REFL_CLAUSE,  EQ_CLAUSES,
          NOT_CLAUSES,  AND_CLAUSES,
          OR_CLAUSES,   IMP_CLAUSES,
          COND_CLAUSES, FORALL_SIMP,
          EXISTS_SIMP,  COND_ID,
          EXISTS_REFL, GSYM EXISTS_REFL,
          EXISTS_UNIQUE_REFL, GSYM EXISTS_UNIQUE_REFL,
          COND_BOOL_CLAUSES,
          literal_I_thm,
          EXCLUDED_MIDDLE,
          ONCE_REWRITE_RULE [DISJ_COMM] EXCLUDED_MIDDLE,
          bool_case_thm,
          NOT_AND,
          SELECT_REFL, SELECT_REFL_2, RES_FORALL_TRUE, RES_EXISTS_FALSE],
   congs = [literal_cong], filter = NONE, ac = [], dprocs = []};


(*---------------------------------------------------------------------------
   Need to rewrite cong. rules to the iterated implication format assumed
   by the simplifier.
 ---------------------------------------------------------------------------*)

local val IMP_CONG = REWRITE_RULE [GSYM AND_IMP_INTRO] IMP_CONG
      val COND_CONG = REWRITE_RULE [GSYM AND_IMP_INTRO] COND_CONG
in
val CONG_ss = SSFRAG
  {name=SOME"CONG",
   congs = [IMP_CONG, COND_CONG, RES_FORALL_CONG, RES_EXISTS_CONG],
   convs = [], rewrs = [], filter=NONE, ac=[], dprocs=[]}
end;


(* ---------------------------------------------------------------------
 * NOT_ss
 *
 * Moving negations inwards, eliminate disjuncts involving negations,
 * eliminate negations on either side of equalities.
 *
 * Previously also contained
 *
 *    |- ~x \/ y = (x ==> y)
 *    |- x \/ ~y = (y ==> x)
 *
 * but that was too dramatic for some ...
 *
 * --------------------------------------------------------------------*)

val NOT_ss =
  named_rewrites "NOT"
    [NOT_IMP,
     DE_MORGAN_THM,
     NOT_FORALL_THM,
     NOT_EXISTS_THM,
     TAUT `(~p = ~q) = (p = q)`];

(*------------------------------------------------------------------------
 * UNWIND_ss
 *------------------------------------------------------------------------*)

val UNWIND_ss = SSFRAG
  {name=SOME "UNWIND",
   convs=[{name="UNWIND_EXISTS_CONV",
           trace=1,
           key=SOME ([],``?x:'a. P``),
           conv=K (K Unwind.UNWIND_EXISTS_CONV)},
          {name="UNWIND_FORALL_CONV",
           trace=1,
           key=SOME ([],``!x:'a. P``),
           conv=K (K Unwind.UNWIND_FORALL_CONV)}],
   rewrs=[],filter=NONE,ac=[],dprocs=[],congs=[]};


(* ----------------------------------------------------------------------
    LET_ss
   ---------------------------------------------------------------------- *)

 val let_cong = prove(
   ``(v:'a = v') ==> (LET (f:'a -> 'b) v = LET f (I v'))``,
   DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC [LET_THM, combinTheory.I_THM])

val let_I_thm = prove(
  ``LET (f : 'a -> 'b) (I x) = f x``,
  REWRITE_TAC [combinTheory.I_THM, LET_THM]);

val LET_ss =
    simpLib.SSFRAG {name = SOME"LET",
                    ac = [], congs = [let_cong], convs = [], filter = NONE,
                    dprocs = [], rewrs = [let_I_thm]}

(* ----------------------------------------------------------------------
    bool_ss
      This is essentially the same as the old REWRITE_TAC []
      with the "basic rewrites" plus:
         - ABS_SIMP removed in favour of BETA_CONV
         - COND_ID added: (P => Q | Q) = Q
         - contextual rewrites for P ==> Q and P => T1 | T2
         - point-wise unwinding under ! and ?

      Beta conversion and "basic rewrites" come from BOOL_ss, while
      the contextual rewrites are found in CONG_ss.  Unwinding comes
      from UNWIND_ss.  This split is done so that users have the
      potential to construct their own custom simpsets more easily.
      For example, inefficient context gathering required for the
      congruence reasoning can be omitted in a custom simpset built
      from BOOL_ss.
   ---------------------------------------------------------------------- *)

val bool_ss = pure_ss ++ BOOL_ss ++ NOT_ss ++ CONG_ss ++ UNWIND_ss



(* ----------------------------------------------------------------------
 * COND_elim_ss
 *
 * Getting rid of as many conditional expression as possible.  Basic
 * strategy is to lift conditional expressions until they have boolean
 * type overall, in which case they can be written out using COND_EXPAND.
 * For goals (which have top-level type of bool), this usually works
 * well, but conditionals underneath lambdas won't disappear, as in
 *    `P (\x. if Q then f x else g x) : bool`
 * The lambda's that appear under foralls, existentials and the like are
 * OK of course because the bodies of such abstractions have boolean type.
 *
 * Application of this simpset can result in completely incomprehensible
 * boolean terms.
 * ---------------------------------------------------------------------- *)


val NESTED_COND = prove(
  ``!p (q:'a) (r:'a) s.
          (COND p (COND p q r) s = COND p q s) /\
          (COND p q (COND p r s) = COND p q s) /\
          (COND p (COND (~p) q r) s = COND p r s) /\
          (COND p q (COND (~p) r s) = COND p q r)``,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC []);

fun celim_rand_CONV tm = let
  val (Rator, Rand) = Term.dest_comb tm
  val proceed = let
    val (f, args) = strip_comb Rator
  in
    not (same_const f conditional) orelse null args orelse
    let
      fun dneg t = (dest_neg t, false) handle HOL_ERR _ => (t, true)
      val fg0 = hd args
      val xg0 = hd (#2 (strip_comb Rand))
      val (fg, fposp) = dneg fg0
      val (xg, xposp) = dneg xg0
    in
      case Term.compare(fg, xg) of
        LESS => false
      | EQUAL => xposp andalso not fposp
      | GREATER => true
    end
  end
in
  (if proceed then REWR_CONV boolTheory.COND_RAND else NO_CONV) tm
end

fun COND_ABS_CONV tm = let
  open Type Rsyntax
  infix |-> THENC
  val {Bvar=v,Body=bdy} = dest_abs tm
  val {cond,larm=x,rarm=y} = Rsyntax.dest_cond bdy
  val b = assert (not o op_mem aconv v o free_vars) cond
  val xf = mk_abs{Bvar=v,Body=x}
  val yf = mk_abs{Bvar=v,Body=y}
  val th1 = INST_TYPE [alpha |-> type_of v, beta |-> type_of x] COND_ABS
  val th2 = SPECL [b,xf,yf] th1
in
  CONV_RULE (RATOR_CONV (RAND_CONV
                           (ABS_CONV (RATOR_CONV (RAND_CONV BETA_CONV) THENC
                                      RAND_CONV BETA_CONV) THENC
                            ALPHA_CONV v))) th2
end handle HOL_ERR _ => failwith "COND_ABS_CONV";


val COND_elim_ss =
  simpLib.SSFRAG {name = SOME"COND_elim",
                  ac = [], congs = [],
                  convs = [{conv = K (K celim_rand_CONV),
                             name = "conditional lifting at rand",
                             key = SOME([], Term`(f:'a -> 'b) (COND P Q R)`),
                             trace = 2},
                            {conv = K (K COND_ABS_CONV),
                             name = "conditional lifting under abstractions",
                             key = SOME([],
                                        Term`\x:'a. COND p (q x:'b) (r x)`),
                             trace = 2}],
                  dprocs = [], filter = NONE,
                  rewrs = [boolTheory.COND_RATOR, boolTheory.COND_EXPAND,
                           NESTED_COND]}

val LIFT_COND_ss = simpLib.SSFRAG
  {name=SOME"LIFT_COND",
   ac = [], congs = [],
   convs = [{conv = K (K celim_rand_CONV),
             name = "conditional lifting at rand",
             key = SOME([], Term`(f:'a -> 'b) (COND P Q R)`),
             trace = 2},
            {conv = K (K COND_ABS_CONV),
             name = "conditional lifting under abstractions",
             key = SOME([], Term`\x:'a. COND p (q x:'b) (r x)`),
             trace = 2}],
   dprocs = [], filter = NONE,
   rewrs = [boolTheory.COND_RATOR, NESTED_COND]}


(* ----------------------------------------------------------------------
 * CONJ_ss
 *
 * A congruence rule for /\.  This allows one side of a conjunction to be
 * assumed while rewriting the other.  This is typically useful when
 * attacking a goal of the form (x = ..) /\ ... x ...
 *
 * Not efficient on terms with many conjunctions chained together
 * ------------------------------------------------------------------------*)

val CONJ_ss = SSFRAG {
  name = SOME"CONJ",
  ac = [],
  congs = [REWRITE_RULE [GSYM AND_IMP_INTRO] (SPEC_ALL boolTheory.AND_CONG)],
  convs = [], dprocs = [], filter = NONE, rewrs = []}

(* ----------------------------------------------------------------------
    A boolean formula normaliser that attempts to create formulas with
    maximum opportunity for UNWIND_ss to eliminate equalities
   ---------------------------------------------------------------------- *)

val DNF_ss = rewrites [FORALL_AND_THM, EXISTS_OR_THM,
                       DISJ_IMP_THM, IMP_CONJ_THM,
                       RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR,
                       GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
                       GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM]


val EQUIV_EXTRACT_ss = simpLib.conv_ss BoolExtractShared.BOOL_EQ_IMP_convdata;

val NORMEQ_CONV = let
  fun c (cf : term list -> term -> thm) (tl : term list) t =
    let
      val (l,r) = dest_eq t
    in
      if null (free_vars l) andalso not (null (free_vars r)) then
        REWR_CONV EQ_SYM_EQ
      else NO_CONV
    end t
in
  { name = "NORMEQ_CONV",
    key = SOME ([] : term list, ``x:'a = y``),
    trace = 2,
    conv = c }
end

val NORMEQ_ss = simpLib.SSFRAG {
  ac = [],
  congs = [],
  convs = [NORMEQ_CONV],
  dprocs = [],
  filter = NONE,
  name = SOME "NORMEQ_ss", rewrs = []}

(* ----------------------------------------------------------------------
    Congruence rules for rewriting on one side or the other of a goal's
    central binary operator
   ---------------------------------------------------------------------- *)

open Type
val x = mk_var("x", alpha)
val x' = mk_var("x'", alpha)
val y = mk_var("y", beta)
val y' = mk_var("y'", beta)
val f = mk_var("f", alpha --> beta --> gamma)
val patternL = DISCH_ALL (AP_THM (AP_TERM f (ASSUME (mk_eq(x,x')))) y)
val patternR = DISCH_ALL (AP_TERM (mk_comb(f,x)) (ASSUME (mk_eq(y,y'))))

val findf = #1 o strip_comb o lhs o #2 o dest_imp

fun SimpL t = Cong (PART_MATCH findf patternL t)
fun SimpR t = Cong (PART_MATCH findf patternR t)
val SimpLHS = SimpL boolSyntax.equality
val SimpRHS = SimpR boolSyntax.equality



val _ = Parse.temp_set_grammars ambient_grammars;

end (* struct *)

(* ---------------------------------------------------------------------
 * EXISTS_NORM_ss
 *
 * Moving existentials
 *    - inwards over disjunctions
 *    - outwards over conjunctions
 *    - outwards from left of implications (??? - do we want this??)
 *    - inwards into right of implications
 * --------------------------------------------------------------------*)

(*
val EXISTS_NORM_ss =
    pure_ss
    |> addrewrs [EXISTS_OR_THM,
        TRIV_AND_EXISTS_THM,
        LEFT_AND_EXISTS_THM,
        RIGHT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM,
        TRIV_EXISTS_IMP_THM];

val EXISTS_IN_ss =
    pure_ss
    |> addrewrs [EXISTS_OR_THM,
        LEFT_EXISTS_AND_THM,
        RIGHT_EXISTS_AND_THM,
        LEFT_EXISTS_IMP_THM,
        TRIV_EXISTS_IMP_THM,
        RIGHT_EXISTS_IMP_THM];

val EXISTS_OUT_ss =
    pure_ss
    |> addrewrs [EXISTS_OR_THM,
        LEFT_AND_EXISTS_THM,
        RIGHT_AND_EXISTS_THM,
        LEFT_IMP_EXISTS_THM,
        RIGHT_IMP_EXISTS_THM];
*)
