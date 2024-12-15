(* ===================================================================== *)
(* FILE          : boolLib.sml                                           *)
(* DESCRIPTION   : boolTheory and related support.                       *)
(* ===================================================================== *)

structure boolLib =
struct

open boolTheory boolSyntax Hol_pp ParseExtras
     Drule Tactical Tactic Thm_cont Conv Rewrite Prim_rec Abbrev DB
     BoundedRewrites TexTokenMap term_tactic

local open TypeBase Ho_Rewrite Psyntax Rsyntax in end

val parse_from_grammars = Parse.parse_from_grammars;

(*---------------------------------------------------------------------------
      Stock the rewriter in Ho_Rewrite with some rules not yet
      proved in boolTheory.
 ---------------------------------------------------------------------------*)

local open HolKernel Ho_Rewrite  (* signature control *)
      structure Parse =
      struct
        open Parse
        val (Type,Term) = parse_from_grammars bool_grammars
      end
      open Parse
in
(*---------------------------------------------------------------------------*)
(* The first conjunct is useful when rewriting assumptions, but not when     *)
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
fun prove_local loc privp (n,th) =
   (if not (!Globals.interactive) then
      print ("Proved triviality ___ \"" ^ String.toString n ^ "\"\n")
    else ();
    DB.store_local {private=privp,loc=loc,class=DB_dtype.Thm} n th;
    th)
fun extract_localpriv (loc,priv,rebindok,acc) attrs =
    case attrs of
        [] => (loc,priv,rebindok,List.rev acc)
      | "unlisted" :: rest => extract_localpriv (loc,true,rebindok,acc) rest
      | "local" :: rest => extract_localpriv (true,priv,rebindok,acc) rest
      | "allow_rebind" :: rest => extract_localpriv (loc,priv,true,acc) rest
      | a :: rest => extract_localpriv (loc,priv,rebindok,a::acc) rest
in
fun save_thm_attrs loc (n, attrs, th) = let
  val (localp,privp,rebindok,attrs) =
      extract_localpriv (false,false,false,[]) attrs
  val save =
      if localp then prove_local loc privp
      else
        fn (n,th) => Theory.gen_save_thm{name=n,private=privp,thm=th,loc=loc}
  val attrf = if localp then ThmAttribute.local_attribute
              else ThmAttribute.store_at_attribute
  val storemod = if rebindok then trace("Theory.allow_rebinds", 1)
                 else (fn f => f)
  fun do_attr a = attrf {thm = th, name = n, attrname = a}
in
  storemod save(n,th) before app do_attr attrs
end
fun store_thm_at loc (n0,t,tac) = let
  val (n, attrs) = ThmAttribute.extract_attributes n0
  val th = Tactical.prove(t,tac)
              handle e => (print ("Failed to prove theorem " ^ n ^ ".\n");
                           Raise e)
in
  save_thm_attrs loc (n,attrs,th)
end
val store_thm = store_thm_at DB.Unknown
fun save_thm_at loc (n0,th) = let
  val (n,attrs) = ThmAttribute.extract_attributes n0
in
  save_thm_attrs loc (n,attrs,th)
end
val save_thm = save_thm_at DB.Unknown

fun new_recursive_definition rcd =
    let val thm = Prim_rec.new_recursive_definition rcd
        val genind = gen_indthm {lookup_ind = TypeBase.induction_of}
    in
      DefnBaseCore.register_indn (genind thm);
      thm
    end

(* ----------------------------------------------------------------------
    Gets a variant of an arbitrary term instead of a single variable.
    Besides the resulting term, it returns also the substitution used to
    get it.
   ---------------------------------------------------------------------- *)

fun variant_of_term vs t =
  let
    open HolKernel
    val check_vars = free_vars t
    val (_,sub) =
        foldl (fn (v, (vs,sub)) =>
                  let
                    val v' = variant vs v
                    val vs' = v'::vs
                    val sub' = if (aconv v v') then sub else
                               (v |-> v')::sub
                  in
                    (vs',sub')
                  end) (vs,[]) check_vars
    val t' = subst sub t
  in
    (t', sub)
  end

end (* local *)

datatype pel = pLeft | pRight | pAbs
fun term_diff t1 t2 =
  let
    open Term HolKernel
    fun recurse p t1 t2 =
      if aconv t1 t2 then []
      else
        case (dest_term t1, dest_term t2) of
            (COMB(f1,x1), COMB (f2,x2)) =>
            if aconv f1 f2 then recurse (pRight :: p) x1 x2
            else if aconv x1 x2 then recurse (pLeft :: p) f1 f2
            else recurse (pLeft :: p) f1 f2 @ recurse (pRight :: p) x1 x2
          | (LAMB(v1,b1), LAMB(v2,b2)) =>
            if aconv v1 v2 then recurse (pAbs :: p) b1 b2
            else if Type.compare(type_of v1,type_of v2) = EQUAL then
              let val v1' = variant (free_vars b2) v1
              in
                recurse (pAbs :: p) b1 (subst [v2 |-> v1'] b2)
              end
            else recurse (pAbs :: p) b1 b2
          | (CONST _, CONST _) => if same_const t1 t2 then []
                                  else [(List.rev p,t1,t2)]
          | _ => [(List.rev p,t1,t2)]
  in
    recurse [] t1 t2
  end

fun tyvar_sequence n =
    let
      val mkvt = Type.mk_vartype
      fun pretty A n =
          if n <= 0 then A
          else if n > 26 then
            pretty (mkvt ("'a" ^ Int.toString (n - 26))::A) (n - 1)
          else
            pretty
              (mkvt ("'" ^ str (Char.chr (Char.ord #"a" + (n - 1))))::A)
              (n - 1)
    in
      pretty [] n
    end



end;
