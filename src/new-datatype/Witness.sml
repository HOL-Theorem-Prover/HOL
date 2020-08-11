structure Witness :> Witness =
struct

open Abbrev;
open NDDB

val fun_all_rule = prove(``!P x.
    fun_all P (\_. x) = P x
``, bossLib.simp[fun_all_def]);

(* GEN_TAC THEN GEN_TAC THEN DISCH_TAC THEN PURE_ONCE_REWRITE_TAC [fun_all_def] THEN GEN_TAC THEN BETA_TAC THEN (W (ACCEPT_TAC o mk_thm)));*)

(************************* rules storage *************************)
fun lookup tyvar (tyvar'::tyvars, h::dict) =
    if tyvar = tyvar' then SOME h
    else lookup tyvar (tyvars, dict)
  | lookup _ _ = NONE;
fun insert (tyvar, value) ([], []) = ([tyvar], [value])
  | insert (tyvar, value) (tyvar'::tyvars, h::dict) =
    if tyvar = tyvar' then (tyvar::tyvars, value::dict)
    else let
      val (x, y) = (insert (tyvar,value) (tyvars, dict))
      in (tyvar'::x, h::y) end;
val all_rules = ref (([]:string list),([]:Thm.thm list));

val _ = (all_rules := insert ("sum_all", sum_all_def) (!all_rules);
all_rules := insert ("list_all", list_all_def) (!all_rules);
all_rules := insert ("prod_all", prod_all_def) (!all_rules);
all_rules := insert ("option_all", option_all_def) (!all_rules);
all_rules := insert ("fun_all", fun_all_rule) (!all_rules));

(*load "finite_mapLib";
all_rules := insert ("FEVERY", finite_mapTheory.FEVERY_DEF)
                    (!all_rules);*)

(*****************************************************************)

fun variant thm = let
  val vars = map type_of ((fst o strip_forall o concl) thm)
  val vars' = map genvar vars
  in SPECL vars' thm
end;

fun resolve q [] thm = []
  | resolve q (rule::rules) thm = let
        val (H, B) = dest_eq (concl rule)
        val (H', H'') = dest_comb H
        val (q', q'') = dest_comb q
        val subst = match_term H' q'
        val H'' = inst (#2 subst) H''
        val d = INST_TY_TERM (match_term q'' H'') (DISCH q thm)
        val rule' = INST_TY_TERM subst rule
        val trans = IMP_TRANS (snd (EQ_IMP_RULE rule')) d
        val hyps = (fst o dest_imp o concl) trans
        val res = PROVE_HYP (ASSUME_CONJS hyps) (UNDISCH trans)
      in res :: (resolve q rules thm)
      end handle _ => resolve q rules thm;

fun is_lit x = (is_const x) orelse (is_var x);
fun dest_lit x = if is_const x then dest_const x else dest_var x;

fun get_rules rules xrules tm =
  if is_abs tm then let
    val var = (genvar o fst o dom_rng o type_of) tm
    in [BETA_CONV (mk_comb (tm, var))] end
  else if is_const tm then
    case lookup (#1 (dest_const tm)) rules of
      NONE => raise ERR "" "unknown all fun"
    | SOME thm => map variant (CONJUNCTS thm)
  else if is_var tm then
    case lookup (#1 (dest_var tm)) xrules of
      NONE => raise ERR "" ""
    | SOME thm => [thm]
  else raise ERR "" "";

fun REMOVE_EQ eq thm =
     PROVE_HYP
    (REFL (rhs eq))
    (INST [(op|-> o dest_eq) eq] thm);

fun leftmost alls xalls [     ] = raise ERR "Witness" "Empty type"
  | leftmost alls xalls (t::ts) =
      prove_all alls xalls t handle _ => leftmost alls xalls ts
and prove_all alls xalls thm = let
   val hs = hyp thm
   val h1 = hd hs handle _ => T
   in   if hs = []  then thm
   else if h1 = T   then prove_all alls xalls (PROVE_HYP TRUTH thm)
   else if is_eq h1 then prove_all alls xalls (REMOVE_EQ h1    thm)
   else let val (ator, _) = strip_comb h1
            val rules = get_rules alls xalls ator
            val res = resolve h1 rules thm
        in leftmost alls xalls res
   end end;


(*fun test q = let
  val tm = Term q
  val var = Term.variant (free_vars tm)
            (mk_var ("x", (fst o dom_rng o type_of) tm))
  val tm' = mk_comb(tm, var)
  val res = prove_all (!all_rules) (ASSUME tm')
  val wit = (snd o dest_comb o concl) res
  val ex = mk_exists(var, tm')
in EXISTS (ex, wit) res
end;
*)

(*****************************************************************)
(*
prove_all (!all_rules) (ASSUME ``sum_all (\x.x=0) (prod_all (list_all P) (list_all Q)) x``)

test`sum_all ($=0) (prod_all (list_all P) (list_all Q))`;
test`option_all P`;
test`sum_all (\_.F) (\_.F)`;
test`fun_all (\_.T)`;

val llrecycle = prove(``!x. ?ll. ll = x:::ll``,
GEN_TAC THEN EXISTS_TAC

Define`llx = 0:::llx`


val all_llist_rule = prove(``P a ==> all_llist P (abs (\x. SOME a))``

*)
(*****************************************************************)


local
fun update_witnesses' [] [] _ _ = []
  | update_witnesses' (NONE::wits) ((SOME t)::results) cs n =
      (SOME (MATCH_MP (el n cs) t))
      :: (update_witnesses' wits results cs (n+1))
  | update_witnesses' (w::wits) (r::results) cs n =
      w :: (update_witnesses' wits results cs (n+1))
in fun update_witnesses cs w r = update_witnesses' w r cs 1
end;

fun foo (a,b) (c,d) = ((a@c), (b@d));

fun update_wits_loop tms ws constrs = let
    (* 1: extract known witnesses as rules  *)
    val wrules = mapfilter (EQT_INTRO o valOf) ws
    val ns = mapfilter(fst o dest_const o rator o concl o valOf)ws
    (* 2: find new witnesses *)
    val app = total (prove_all (foo (!all_rules) (ns, wrules)) ([],[]))
    val ws' = map app tms
    (* 3: update known witnesses *)
    val func = fn (i, (wit, res)) => (
        if (not (isSome wit)) andalso (isSome res) then
           (SOME (MATCH_MP (el (i+1) constrs) (valOf res)))
          else wit)
    val ws'' = mapi (curry func) (zip ws ws')
    (* 4: emptiness check *)
    val _ = if map isSome ws = map isSome ws''
            then raise ERR "gen_witness_repr" "Empty type"
            else ()
 in if   List.all isSome ws'
    then ws''
    else update_wits_loop tms ws'' constrs
end;


fun fix_ind_wits thm = let
  val (a, b) = (dest_comb o concl) thm
  val sub = map (fn x=> x|->((mk_arb o type_of)x)) (free_vars b)
  val thm = INST sub thm
  val (a, b) = (dest_comb o concl) thm
  val var = Term.variant (free_vars a)
            (mk_var ("x", type_of b))
  val tm' = mk_comb(a, var)
  val ex = mk_exists(var, tm')
in EXISTS (ex, b) thm
end;

fun find_inductive_witnesses a b c = let
    val res = update_wits_loop a b c
  in map (fix_ind_wits o valOf) res
end;

(*
fun test2 thm = let
  val res = prove_all (!all_rules) thm
  val wit = (snd o dest_comb o concl) res
  val sub = map (fn x=> x|->((mk_arb o type_of)x)) (free_vars wit)
in INST sub res
end;


val Hyps = [``(list_all P x):bool``, ``(sum_all (XX:'a list->bool) YY x):bool``];


val ws = [NONE, NONE];
val constrs = [mk_thm([], ``!P x. (list_all P x) ==> (XX x)``),
mk_thm([], ``!XX YY x. (sum_all (XX:'a list->bool) YY x) ==> ZZ x``)]
val Hyps = map(fst o dest_imp o snd o strip_forall o concl) constrs
val tms = (map ASSUME Hyps)
update_wits_loop tms ws constrs

prove_all alls xalls thm


val ax = mk_thm([], ``!P x. (list_all P x) ==> (XX x)``);
UNDISCH (SPEC_ALL ax);

*)


end;
