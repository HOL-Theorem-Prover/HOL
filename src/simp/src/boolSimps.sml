structure boolSimps :> boolSimps =
struct

open HolKernel Parse simpLib
     basicHol90Lib liteLib Ho_theorems pureSimps Ho_rewrite;
infix THEN THENQC ++;

val (Type,Term) = parse_from_grammars boolTheory.bool_grammars
fun -- q x = Term q
fun == q x = Type q

(* ---------------------------------------------------------------------
 * bool_ss
 *   This is essentially the same as the old REWRITE_TAC []
 *   with the "basic rewrites" plus:
 *      - ABS_SIMP removed in favour of BETA_CONV
 *      - COND_ID added: (P => Q | Q) = Q
 *      - contextual rewrites for P ==> Q and P => T1 | T2 added
 *   The convs and "basic rewrites" come from BOOL_ss, while the
 *   contextual rewrites are found in CONG_ss.  This split is done so
 *   that the potential inefficient context gathering required for the
 *   congruence reasoning can be omitted in a custom simpset built from
 *   BOOL_ss.
 * --------------------------------------------------------------------*)

fun BETA_CONVS tm = (RATOR_CONV BETA_CONVS THENQC BETA_CONV) tm

fun comb_ETA_CONV t =
    (if (not (Dsyntax.is_exists t orelse Dsyntax.is_forall t
              orelse Dsyntax.is_select t)) then
         RAND_CONV ETA_CONV
     else NO_CONV) t

val BOOL_ss = SIMPSET
  {convs=[{name="BETA_CONV (beta reduction)",
           trace=2,
           key=SOME ([],(--`(\x:'a. y:'b) z`--)),
	   conv=K (K BETA_CONV)},
(* kls. This doesn't make much sense in just the "bool" theory; if you
   are not using pairs, then rewriting with boolTheory.LET_DEF will suffice!
	  {name = "let_CONV (reduction of let terms)",
	   trace = 2,
	   key = SOME ([], (--`$LET (f:'a->'b) x`--)),
	   conv = K (K let_CONV)},
*)
          {name = "ETA_CONV (eta reduction)",
           trace = 2,
           key = SOME ([],
                       --`(f:('a->'b)->'c) (\x:'a. (g:'a->'b) x)`--),
           conv = K (K comb_ETA_CONV)},
          {name = "ETA_CONV (eta reduction)",
           trace = 2,
           key = SOME ([], --`\x:'a. \y:'b. (f:'a->'b->'c) x y`--),
           conv = K (K (ABS_CONV ETA_CONV))}],
   rewrs=[REFL_CLAUSE,  EQ_CLAUSES,
          NOT_CLAUSES,  AND_CLAUSES,
          OR_CLAUSES,   IMP_CLAUSES,
          COND_CLAUSES, FORALL_SIMP,
          EXISTS_SIMP,  COND_ID,
          EXISTS_REFL, GSYM EXISTS_REFL,
          EXISTS_UNIQUE_REFL, GSYM EXISTS_UNIQUE_REFL,
          COND_BOOL_CLAUSES,
          EXCLUDED_MIDDLE,
          ONCE_REWRITE_RULE [DISJ_COMM] EXCLUDED_MIDDLE,
          NOT_AND, ONCE_REWRITE_RULE [CONJ_COMM] EXCLUDED_MIDDLE,
          SELECT_REFL, Ho_theorems.SELECT_REFL_2],
   congs = [], filter = NONE, ac = [], dprocs = []};

val CONG_ss = SIMPSET
  {convs = [], rewrs = [], congs = [IMP_CONG, COND_CONG],
   filter=NONE, ac=[], dprocs=[]};

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
 * but the translation to implications was too dramatic for some ...
 *
 * --------------------------------------------------------------------*)

val NOT_ss = rewrites [NOT_IMP,
                       DE_MORGAN_THM,
                       NOT_FORALL_THM,
                       NOT_EXISTS_THM,
                       TAUT (--`(~p = ~q) = (p = q)`--)];

(*------------------------------------------------------------------------
 * UNWIND_ss
 *------------------------------------------------------------------------*)

val UNWIND_ss = SIMPSET
  {convs=[{name="UNWIND_EXISTS_CONV",
           trace=1,
           key=SOME ([],(--`?x:'a. P`--)),
           conv=K (K Unwind.UNWIND_EXISTS_CONV)},
          {name="UNWIND_FORALL_CONV",
           trace=1,
           key=SOME ([],(--`!x:'a. P`--)),
           conv=K (K Unwind.UNWIND_FORALL_CONV)}],
   rewrs=[],filter=NONE,ac=[],dprocs=[],congs=[]};


val bool_ss = pure_ss ++ BOOL_ss ++ NOT_ss ++ CONG_ss ++ UNWIND_ss;



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


val COND_COND_SAME = prove(
  Term`!P (f:'a->'b) g x y. 
        (COND P f g) (COND P x y) 
           = 
        COND P (f x) (g y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC []);

fun celim_rand_CONV tm = let
  val {Rand, Rator} = dest_comb tm
  val (f, _) = strip_comb Rator
  val proceed = #Name (dest_const f) <> "COND" handle HOL_ERR _ => true
in
  (if proceed then REWR_CONV boolTheory.COND_RAND else NO_CONV) tm
end

val COND_elim_ss =
  simpLib.SIMPSET {ac = [], congs = [],
                   convs = [{conv = K (K celim_rand_CONV),
                             name = "conditional lifting at rand",
                             key = SOME([], Term`(f:'a -> 'b) (COND P Q R)`),
                             trace = 2}],
                   dprocs = [], filter = NONE,
                   rewrs = [boolTheory.COND_RATOR, boolTheory.COND_EXPAND,
                            COND_COND_SAME]}

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
