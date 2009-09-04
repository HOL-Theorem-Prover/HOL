
open HolKernel Parse boolLib bossLib

val _ = new_theory("env")


open bossLib
open pairTheory
open pairLib
open pairTools
open pairSyntax
open pred_setTheory
open pred_setLib
open listTheory
open stringTheory
open sumTheory
open simpLib
open stringLib
open numLib
open metisLib
open setLemmasTheory

(* defns about environments *)

val ENV_UPDATE_def = save_thm("ENV_UPDATE_def",Define
    `ENV_UPDATE (e:string -> 'state -> bool) (Q:string) (s:'state -> bool) = \q. if (q=Q) then s else e q`)

val _ = add_rule {term_name = "ENV_UPDATE", fixity = Suffix 2503,
     pp_elements = [TOK "[[[", TM, TOK "<--",TM, TOK "]]]"],
     paren_style = OnlyIfNecessary,
     block_style = (AroundSamePrec, (PP.INCONSISTENT, 0))}

(* initially had BOTTOMSET instead of {} but that causes problems when evaluating concrete environments where I would like all empty
environments to evaluate to the same thing, rather than not evaluate at all. Using {} is not as satisfactory theoretically but more
practical *)
val EMPTY_ENV = Define `EMPTY_ENV = \(s:string). {}`


(* thms about environments *)

val env1a = prove(``!x Q Q'. ~(Q=Q') ==> (!e X X'. e[[[Q<--X]]][[[Q'<--X']]]x = e[[[Q'<--X']]][[[Q<--X]]]x)``,RW_TAC std_ss [ENV_UPDATE_def] THEN ASSUM_LIST PROVE_TAC)

val ENV_SWAP = save_thm("ENV_SWAP",prove (``!e Q Q' X X'. ~(Q=Q') ==> (e[[[Q<--X]]][[[Q'<--X']]] = e[[[Q'<--X']]][[[Q<--X]]])``,
		RW_TAC std_ss [ENV_UPDATE_def,EXTENSION,SET_SPEC]
		THEN RW_TAC std_ss [FUN_EQ_CONV ``(\q. (if q = Q' then X' else (if q = Q then X else e q))) =
                                (\q. (if q = Q then X else (if q = Q' then X' else e q)))``,env1a,ENV_UPDATE_def]
                THEN ASSUM_LIST PROVE_TAC))

val ENV_UPDATE = save_thm("ENV_UPDATE",prove(``!Q e X Y. e[[[Q<--X]]][[[Q<--Y]]] = e[[[Q<--Y]]]``,RW_TAC std_ss [ENV_UPDATE_def]))

val ENV_EVAL = save_thm("ENV_EVAL",prove(``!e Q X. e[[[Q<--X]]] Q = X``,SIMP_TAC std_ss [ENV_UPDATE_def]))

val ENV_UPDATE_INV = save_thm("ENV_UPDATE_INV",prove(``!e Q Q' X. ~(Q=Q') ==> (e[[[Q'<--X]]] Q = e Q)``,SIMP_TAC std_ss [ENV_UPDATE_def]))

val ENV_EVAL_EQ_INV = save_thm("ENV_EVAL_EQ_INV",prove(``!e e' Q P X. (Q=P) ==> (e[[[Q<--X]]] P = e'[[[Q<--X]]] P)``,
					    SIMP_TAC std_ss [ENV_UPDATE_def]))

val ENV_EVAL_NEQ_INV = save_thm("ENV_EVAL_NEQ_INV",prove(``!e e' Q P X. ~(Q=P) ==> ((e[[[Q<--X]]] P = e'[[[Q<--X]]] P) = (e P = e' P))``,
					    SIMP_TAC std_ss [ENV_UPDATE_def]))

val EMPTY_ENV_MAP = save_thm("EMPTY_ENV_MAP",prove(``!x y. EMPTY_ENV x = EMPTY_ENV y``,SIMP_TAC std_ss [EMPTY_ENV]))

val ENV_UPDATE_BOTH_INV = save_thm("ENV_UPDATE_BOTH_INV",prove(``!e Q Q' X Y. ~(Q=Q') ==> (e[[[Q'<--X]]] Q = e[[[Q'<--Y]]] Q)``,SIMP_TAC std_ss [ENV_UPDATE_def]))

val ENV_CASES = save_thm("ENV_CASES",prove(``!e e' P Q X Y. e[[[P<--X]]] Q SUBSET e'[[[P<--Y]]] Q = if (Q=P) then X SUBSET Y else e Q SUBSET e' Q``,REPEAT STRIP_TAC THEN SIMP_TAC std_ss [ENV_UPDATE_def,SUBSET_DEF] THEN REPEAT COND_CASES_TAC THEN SIMP_TAC std_ss []))

val _ = export_theory()