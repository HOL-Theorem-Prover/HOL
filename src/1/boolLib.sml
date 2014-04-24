(* ===================================================================== *)
(* FILE          : boolLib.sml                                           *)
(* DESCRIPTION   : boolTheory and related support.                       *)
(* ===================================================================== *)

structure boolLib =
struct

open boolTheory boolSyntax Hol_pp ParseExtras
     Drule Tactical Tactic Thm_cont Conv Rewrite Prim_rec Abbrev DB
     BoundedRewrites TexTokenMap ThmSetData

local open DefnBase TypeBase Ho_Rewrite Psyntax Rsyntax in end

val parse_from_grammars = Parse.parse_from_grammars;

(* ----------------------------------------------------------------------
    Update DefnBase with some extra congruence rules
   ---------------------------------------------------------------------- *)

val _ = DefnBase.write_congs (DefnBase.read_congs() @
                              map (REWRITE_RULE [AND_IMP_INTRO])
                                  [RES_FORALL_CONG, RES_EXISTS_CONG])

(*---------------------------------------------------------------------------
      Stock the rewriter in Ho_Rewrite with some rules not yet
      proved in boolTheory.
 ---------------------------------------------------------------------------*)

local open HolKernel Ho_Rewrite  (* signature control *)
in
(*---------------------------------------------------------------------------*)
(* The first canjunct is useful when rewriting assumptions, but not when     *)
(* rewriting conclusion, since it prevents stripping. Better rewrite on      *)
(* conclusions is IF_THEN_T_IMP.                                             *)
(*---------------------------------------------------------------------------*)

val COND_BOOL_CLAUSES =
  prove(``(!b e. (if b then T else e) = (b \/ e)) /\
          (!b t. (if b then t else T) = (b ==> t)) /\
          (!b e. (if b then F else e) = (~b /\ e)) /\
          (!b t. (if b then t else F) = (b /\ t))``,
REPEAT (STRIP_TAC ORELSE COND_CASES_TAC ORELSE EQ_TAC)
  THEN RULE_ASSUM_TAC (REWRITE_RULE[F_DEF])
  THEN (ACCEPT_TAC TRUTH ORELSE TRY(FIRST_ASSUM MATCH_ACCEPT_TAC))
  THEN ASM_REWRITE_TAC[]);

val _ = Ho_Rewrite.add_implicit_rewrites [COND_BOOL_CLAUSES];

val IF_THEN_T_IMP =  (* better rewrite for RW_TAC *)
  prove(``!b e. (if b then T else e) = (~b ==> e)``,
REPEAT (STRIP_TAC ORELSE COND_CASES_TAC ORELSE EQ_TAC)
  THEN RULE_ASSUM_TAC (REWRITE_RULE[F_DEF])
  THEN (ACCEPT_TAC TRUTH ORELSE TRY(FIRST_ASSUM MATCH_ACCEPT_TAC))
  THEN ASM_REWRITE_TAC[]);

(* ------------------------------------------------------------------------- *)
(* Alternative version of unique existence, slated for boolTheory.           *)
(* ------------------------------------------------------------------------- *)

val EXISTS_UNIQUE_ALT = prove(
(* store_thm( "EXISTS_UNIQUE_ALT", *)
 ``!P:'a->bool. (?!x. P x) = ?x. !y. P y = (x = y)``,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC ``x:'a``) ASSUME_TAC) THEN
    EXISTS_TAC ``x:'a`` THEN GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[],
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_ACCEPT_TAC],
    DISCH_THEN(X_CHOOSE_TAC ``x:'a``) THEN
    ASM_REWRITE_TAC[GSYM EXISTS_REFL] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN REFL_TAC]);;


(* ------------------------------------------------------------------------- *)
(* NB: this one is true intuitionistically and intensionally.                *)
(* ------------------------------------------------------------------------- *)

val UNIQUE_SKOLEM_ALT = prove
(*  "UNIQUE_SKOLEM_ALT", *)
 (``!P:'a->'b->bool. (!x. ?!y. P x y) = ?f. !x y. P x y = (f x = y)``,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_ALT, SKOLEM_THM]);


(* ------------------------------------------------------------------------- *)
(* and this one intuitionistically and extensionally.                        *)
(* ------------------------------------------------------------------------- *)

val UNIQUE_SKOLEM_THM = prove
(* store_thm("UNIQUE_SKOLEM_THM", *)
(``!P. (!x:'a. ?!y:'b. P x y) = ?!f. !x. P x (f x)``,
 GEN_TAC
  THEN REWRITE_TAC[EXISTS_UNIQUE_THM, SKOLEM_THM, FORALL_AND_THM]
  THEN EQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)
  THEN ASM_REWRITE_TAC[] THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC ``x:'a`` THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC ``x:'a`` THEN ASM_REWRITE_TAC[],
    MAP_EVERY X_GEN_TAC [``x:'a``, ``y1:'b``, ``y2:'b``]
    THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC ``f:'a->'b``) THEN
    SUBGOAL_THEN ``(\z. if z=x then y1 else (f:'a->'b) z)
                 = (\z. if z=x then y2 else (f:'a->'b) z)`` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[],
      DISCH_THEN(MP_TAC o C AP_THM ``x:'a``) THEN REWRITE_TAC[BETA_THM]]])



end (* local open *)

val def_suffix = ref "_def"

local
open Feedback Theory
fun resolve_storename s = let
  open Substring
  val (bracketl,rest) = position "[" (full s)
in
  if isEmpty rest then (s,[])
  else let
    val (names,bracketr) = position "]" (slice(rest,1,NONE))
  in
    if size bracketr <> 1 then
      raise mk_HOL_ERR "boolLib" "resolve_storename"
            ("Malformed theorem-binding specifier: "^s)
    else
      (string bracketl, String.fields (fn c => c = #",") (string names))
  end
end
in
fun save_thm_attrs fname (n, attrs, th) = let
  fun do_attr a = let
    val storefn = valOf (ThmSetData.data_storefn a)
                        handle Option => raise mk_HOL_ERR "boolLib" fname
                                               ("No attribute with name "^a)
    val exportfn = ThmSetData.data_exportfn a
  in
    storefn n;
    case exportfn of
        NONE => ()
      | SOME ef => ef (current_theory()) [th]
  end
in
  Theory.save_thm(n,th) before app do_attr attrs
end
fun store_thm(n0,t,tac) = let
  val (n, attrs) = resolve_storename n0
  val th = Tactical.prove(t,tac)
              handle e => (print ("Failed to prove theorem " ^ n ^ ".\n");
                           Raise e)
in
  save_thm_attrs "store_thm" (n,attrs,th)
end
fun save_thm(n0,th) = let
  val (n,attrs) = resolve_storename n0
in
  save_thm_attrs "save_thm" (n,attrs,th)
end
end (* local *)
end;
