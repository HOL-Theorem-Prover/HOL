structure boolTools :> boolTools =
struct

open HolKernel Parse basicHol90Lib
infix ORELSEC THEN;

type hol_type = Type.hol_type
type term = Term.term
type thm = Thm.thm
type tactic = Abbrev.tactic;
type conv = Abbrev.conv;

fun BTOOLS_ERR{func,mesg} =
      HOL_ERR{origin_structure = "BoolTools",
              origin_function = func,
              message = mesg};


(*--------------------------------------------------------------------------
 * I am not sure if this really does give NNF, but it is useful
 * interactively, especially when doing proof by contradiction.
 *--------------------------------------------------------------------------*)
local fun bval w t =
        (type_of t = Type.bool)
        andalso (can (find_term is_var) t) andalso (free_in t w)
in val TAUT_CONV =
       C (curry prove)
         (REPEAT GEN_TAC THEN (REPEAT o CHANGED_TAC o W)
           (C (curry op THEN) (Rewrite.REWRITE_TAC[]) o BOOL_CASES_TAC o hd
                               o sort free_in
                               o W(find_terms o bval) o snd))
   end;

val TCONV = TAUT_CONV o Parse.Term

val NNF_CONV =
   let val DE_MORGAN = REWRITE_CONV
                        [TCONV`~(x==>y) = (x /\ ~y)`,
                         TCONV`~x \/ y = (x ==> y)`,DE_MORGAN_THM]
       val QUANT_CONV = NOT_EXISTS_CONV ORELSEC NOT_FORALL_CONV
   in REDEPTH_CONV (QUANT_CONV ORELSEC CHANGED_CONV DE_MORGAN)
   end;

val NNF_TAC = CONV_TAC NNF_CONV;


fun WEAKEN_TAC (K:term list):tactic = fn  (G,a) =>
   if (Lib.all (Lib.C mem G) K)
   then ([(K,a)], fn [th] => itlist ADD_ASSUM (set_diff G K) th)
   else raise BTOOLS_ERR{func="WEAKEN_TAC", mesg = "Not subset"};


(*---------------------------------------------------------------------------
 * Handling lets
 *
 * The following is support for "pulling" lets to the top level of the term;
 * and a tactic that will then plunk the let-binding on the assumptions.
 * Pulling lets to the top level is done via higher-order rewriting.
 *---------------------------------------------------------------------------*)
val PULL_LET = prove
(Term`!(P:'b->bool) (M:'a) N. P (let x = M in N x) = (let x = M in P (N x))`,
 Rewrite.REWRITE_TAC[boolTheory.LET_DEF]
  THEN BETA_TAC THEN Rewrite.REWRITE_TAC[]);


val LET_THM = BETA_RULE
    (AP_THM (AP_THM boolTheory.LET_DEF (Term`f:'a->'b`)) (Term`x:'a`));

val GAP_TAC:tactic = W (ACCEPT_TAC o mk_thm);

fun NTAC n tac = funpow n (curry (op THEN) tac) ALL_TAC;

fun Sterm q = let val tmp = !Globals.show_types
                  val _ = Globals.show_types := true
              in Lib.K (Parse.print_term(Parse.Term q))
                       (Globals.show_types := tmp);
                 Lib.say"\n"
              end;

fun DEST_IFF thm =
   let val (th1,th2) = EQ_IMP_RULE thm
   in {ltor = th1, rtol = th2}
   end;


fun GEN_CASES_TAC case_thm:tactic = fn (g as (asl,w)) =>
   let val {Bvar,Body} = dest_forall w
   in (GEN_TAC THEN STRUCT_CASES_TAC (ISPEC Bvar case_thm)) g
   end;

(*---------------------------------------------------------------------------
 * Slightly more general versions of MATCH_MP_TAC and
 * "FIRST_ASSUM MATCH_MP_TAC".
 *---------------------------------------------------------------------------*)
local
val ALL_OUT_CONV = REDEPTH_CONV (RIGHT_IMP_FORALL_CONV ORELSEC
                                 RIGHT_AND_FORALL_CONV ORELSEC
                                 RIGHT_OR_FORALL_CONV)
in
  fun BC_TAC th = MATCH_MP_TAC
                    (Rewrite.REWRITE_RULE[TCONV`x==>y==>z = x/\y ==> z`]
                                         (CONV_RULE ALL_OUT_CONV th))
  val ASM_BC_TAC = FIRST_ASSUM BC_TAC
end;

fun variants away0 vlist =
 rev_itlist (fn v => fn (V,away) =>
    let val v' = variant away v in  (v'::away, v'::V) end)
 vlist ([],away0);



(*---------------------------------------------------------------------------
 * Some useful theorems.
 *---------------------------------------------------------------------------*)
val COND_CONG = prove(
--`!P P' (x:'a) x' y y'.
      (P = P') /\ (P'  ==> (x = x')) /\
                  (~P' ==> (y = y'))
      ==> ((P => x | y) = (P' => x' | y'))`--,
 REPEAT STRIP_TAC THEN
 REPEAT COND_CASES_TAC THEN
 REPEAT RES_TAC);


val LET_CONG = prove(
--`!f (g:'a->'b) M M'.
   (M = M') /\
   (!x:'a. (x = M') ==> (f x = g x))
   ==>
  (LET f M = LET g M')`--,
REPEAT STRIP_TAC
 THEN REWRITE_TAC[boolTheory.LET_DEF]
 THEN BETA_TAC
 THEN RES_TAC
 THEN ASM_REWRITE_TAC[]);


val WIMP_CONG = prove(
--`!x y y'. (x=x) /\
            (x ==> (y = y'))
            ==>
            (x ==> y = x ==> y')`--,
REPEAT GEN_TAC
 THEN ASM_CASES_TAC(--`x:bool`--)
 THEN ASM_REWRITE_TAC[]);


val IMP_CONG = prove(
--`!x x' y y'. (x=x') /\
               (x' ==> (y = y'))
               ==>
               (x ==> y = x' ==> y')`--,
REPEAT GEN_TAC
 THEN BOOL_CASES_TAC(--`x':bool`--)
 THEN BOOL_CASES_TAC(--`x:bool`--)
 THEN REWRITE_TAC[]);

end;
