structure boolSimps :> boolSimps =
struct

open HolKernel Parse simpLib
     basicHol90Lib liteLib Ho_theorems pureSimps Ho_rewrite;
infix THENQC ++;

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

val bool_ss = pure_ss ++ BOOL_ss ++ CONG_ss;


(* ---------------------------------------------------------------------
 * NOT_ss
 *
 * Moving negations inwards, eliminate disjuncts incolving negations,
 * eliminate negations on either side of equalities.
 * --------------------------------------------------------------------*)

val NOT_ss = rewrites [NOT_IMP,
                         DE_MORGAN_THM,
                         NOT_FORALL_THM,
                         NOT_EXISTS_THM,
                         TAUT (--`~x \/ y = (x ==> y)`--),
                         TAUT (--`x \/ ~y = (y ==> x)`--),
                         TAUT(--`(~p = ~q) = (p = q)`--)];


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
