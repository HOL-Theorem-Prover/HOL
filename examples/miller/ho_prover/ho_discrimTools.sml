(* non-interactive mode
*)
structure ho_discrimTools :> ho_discrimTools =
struct
open HolKernel Parse boolLib;

(* interactive mode
val () = loadPath := union ["..", "../finished"] (!loadPath);
val () = app load
  ["bossLib",
   "realLib",
   "rich_listTheory",
   "arithmeticTheory",
   "numTheory",
   "pred_setTheory",
   "pairTheory",
   "combinTheory",
   "listTheory",
   "dividesTheory",
   "primeTheory",
   "gcdTheory",
   "probLib",
   "HurdUseful"];
val () = show_assums := true;
*)

open hurdUtils ho_basicTools;

infixr 0 oo ## ++ << || THENC ORELSEC THENR ORELSER;
infix 1 >>;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val !! = REPEAT;

(* ------------------------------------------------------------------------- *)
(* Type/term substitutions                                                   *)
(* ------------------------------------------------------------------------- *)

val empty_raw_subst : raw_substitution = (([], empty_tmset), ([], []));

fun raw_match' tm1 tm2 ((tmS, tmIds), (tyS, tyIds)) =
  raw_match tyIds tmIds tm1 tm2 (tmS, tyS);

fun type_raw_match ty1 ty2 (sub : raw_substitution) =
  let
    val tm1 = mk_const ("NIL", mk_type ("list", [ty1]))
    val tm2 = mk_const ("NIL", mk_type ("list", [ty2]))
  in
    raw_match' tm1 tm2 sub
  end;

val finalize_subst : raw_substitution -> substitution = norm_subst;

(* ------------------------------------------------------------------------- *)
(* A term discriminator.                                                     *)
(* ------------------------------------------------------------------------- *)

datatype pattern
  = COMB_BEGIN
  | COMB_END
  | ABS_BEGIN of hol_type
  | ABS_END
  | CONSTANT of term
  | BVAR of int
  | FVAR of term * int list;

fun pat_eq p1 p2 =
  case (p1,p2) of
      (COMB_BEGIN, COMB_BEGIN) => true
    | (COMB_END, COMB_END) => true
    | (ABS_BEGIN ty1, ABS_BEGIN ty2) => Type.compare(ty1,ty2) = EQUAL
    | (ABS_END, ABS_END) => true
    | (CONSTANT t1, CONSTANT t2) => aconv t1 t2
    | (BVAR i1, BVAR i2) => i1 = i2
    | (FVAR p1, FVAR p2) => pair_eq aconv equal p1 p2
    | _ => false

datatype 'a discrim = DISCRIM of int * (pattern, 'a) tree list;

val empty_discrim = DISCRIM (0, []);
fun discrim_size (DISCRIM (i, _)) = i;

local
  val bv_prefix = "bv";

  fun advance COMB_BEGIN state = state
    | advance COMB_END (bvs, s1 :: s2 :: srest) =
    (bvs, mk_comb (s2, s1) :: srest)
    | advance (ABS_BEGIN ty) (bvs, stack) =
    let
      val bv = mk_var (mk_string_fn bv_prefix [int_to_string (length bvs)], ty)
    in
      (bv :: bvs, stack)
    end
    | advance ABS_END (bv :: bvs, s1 :: stack) = (bvs, mk_abs (bv, s1) :: stack)
    | advance (CONSTANT tm) (bvs, stack) = (bvs, tm :: stack)
    | advance (BVAR n) (bvs, stack) = (bvs, mk_bv bvs n :: stack)
    | advance (FVAR fvc) (bvs, stack) = (bvs, mk_ho_pat bvs fvc :: stack)
    | advance _ _ = raise BUG "pats_to_term" "not a valid pattern list"

  fun final (_, [tm]) = tm
    | final _ = raise BUG "pats_to_term" "not a complete pattern list"

  fun final_a a state = (final state, a)
in
  fun pats_to_term_bvs (bvs, pats) = final (trans advance (bvs, []) pats)
  fun pats_to_term pats = pats_to_term_bvs ([], pats)
  fun dest_discrim (DISCRIM (_, d)) =
    flatten (map (tree_trans advance final_a ([], [])) d)
end;

fun tm_pat_break (bvs, RIGHT tm :: rest) =
  if is_bv bvs tm then
    (bvs, LEFT (BVAR (dest_bv bvs tm)) :: rest)
  else if is_ho_pat bvs tm then
    (bvs, LEFT (FVAR (dest_ho_pat bvs tm)) :: rest)
  else
    (case dest_term tm of CONST _
       => (bvs, LEFT (CONSTANT tm) :: rest)
     | COMB (Rator, Rand)
       => (bvs,
           LEFT COMB_BEGIN :: RIGHT Rator :: RIGHT Rand ::
           LEFT COMB_END :: rest)
     | LAMB (Bvar, Body)
       => (Bvar :: bvs,
           LEFT (ABS_BEGIN (type_of Bvar)) :: RIGHT Body ::
           LEFT ABS_END :: rest)
     | VAR _ => raise BUG "tm_pat_break" "shouldn't be a var")
  | tm_pat_break (_, []) =
  raise BUG "tm_pat_break" "nothing to break"
  | tm_pat_break (_, LEFT _::_) =
  raise BUG "tm_pat_break" "can't break apart a pattern!";

fun tm_pat_correct ABS_END ((_ : term) :: bvs) = bvs
  | tm_pat_correct ABS_END [] =
  raise BUG "tm_pat_correct" "no bvs left at an ABS_END"
  | tm_pat_correct _ bvs = bvs;

local
  fun tm_pats res (_, []) = res
    | tm_pats res (bvs, LEFT p :: rest) =
    tm_pats (p :: res) (tm_pat_correct p bvs, rest)
    | tm_pats res unbroken =
    tm_pats res (tm_pat_break unbroken)
in
  fun term_to_pats_bvs (bvs, tm) = rev (tm_pats [] (bvs, [RIGHT tm]))
  fun term_to_pats tm = term_to_pats_bvs ([], tm)
end;

local
  fun add a ts [] = LEAF a :: ts
    | add a [] (pat :: next) = [BRANCH (pat, add a [] next)]
    | add a ((b as BRANCH (pat', ts')) :: rest) (ps as pat :: next) =
        if pat_eq pat pat' then BRANCH (pat', add a ts' next) :: rest
        else b :: add a rest ps
    | add _ (LEAF _::_) (_::_) =
    raise BUG "discrim_add" "expected a branch, got a leaf"
in
  fun discrim_add (tm, a) (DISCRIM (i, d)) =
    DISCRIM (i + 1, add a d (term_to_pats tm));
end;

fun mk_discrim l = trans discrim_add empty_discrim l;

fun pat_ho_match _ (FVAR _) _ =
  raise BUG "pat_ho_match" "can't match variables"
  | pat_ho_match sub_thks COMB_BEGIN (_, COMB_BEGIN) = sub_thks
  | pat_ho_match (sub, thks) (ABS_BEGIN ty) (_, ABS_BEGIN ty') =
  (type_raw_match ty ty' sub, thks)
  | pat_ho_match (sub, th1 :: th2 :: thks) COMB_END (_, COMB_END) =
  (sub, (fn () => MK_COMB (th2 (), th1 ())) :: thks)
  | pat_ho_match (sub, th :: thks) ABS_END (bv :: _, ABS_END) =
  (sub, (fn () => MK_ABS (GEN bv (th ()))) :: thks)
  | pat_ho_match (sub, thks) (BVAR n) (bvs, BVAR n') =
  if n = n' then (sub, (fn () => REFL (mk_bv bvs n)) :: thks)
  else raise ERR "pat_ho_match" "different bound vars"
  | pat_ho_match (sub, thks) (CONSTANT c) (_, CONSTANT c') =
  (raw_match' c c' sub, (fn () => REFL c') :: thks)
  | pat_ho_match _ _ _ =
  raise ERR "pat_ho_match" "pats fundamentally different";

local
  fun advance (FVAR (fv, fbs)) ((bvs, RIGHT tm::rest), (sub, thks)) =
    let
      val (sub', thk') = ho_raw_match (fv, fbs) (bvs, tm) sub
    in
      ((bvs, rest), (sub', thk' :: thks))
    end
    | advance pat (state as (_, RIGHT _::_), ho_sub) =
    advance pat (tm_pat_break state, ho_sub)
    | advance pat ((bvs, LEFT pat' :: rest), ho_sub) =
    let
      val ho_sub' = pat_ho_match ho_sub pat (bvs, pat')
    in
      ((tm_pat_correct pat' bvs, rest), ho_sub')
    end
    | advance _ ((_, []), _) =
    raise BUG "discrim_ho_match" "no pats left in list"

  fun finally a ((_, []), (sub, [thk])) =
    SOME ((finalize_subst sub, fn () => SYM (thk ())), a)
    | finally _ _ = raise BUG "discrim_ho_match" "weird state at end"

  fun tree_match tm =
    tree_partial_trans
    (fn x => total (advance x))
    finally
    (([], [RIGHT tm]), (empty_raw_subst, []))
in
  fun discrim_ho_match (DISCRIM (_, d)) tm =
    (flatten o map (tree_match tm)) d
  handle (h as HOL_ERR _) => raise err_BUG "discrim_ho_match" h;
end;

fun pat_fo_match _ (FVAR _) _ =
  raise BUG "pat_fo_match" "can't match variables"
  | pat_fo_match sub COMB_BEGIN COMB_BEGIN = sub
  | pat_fo_match sub (ABS_BEGIN ty) (ABS_BEGIN ty') = type_raw_match ty ty' sub
  | pat_fo_match sub COMB_END COMB_END = sub
  | pat_fo_match sub ABS_END ABS_END = sub
  | pat_fo_match sub (BVAR n) (BVAR n') =
  if n = n' then sub else raise ERR "pat_fo_match" "different bound vars"
  | pat_fo_match sub (CONSTANT c) (CONSTANT c') = raw_match' c c' sub
  | pat_fo_match _ _ _ =
  raise ERR "pat_fo_match" "pats fundamentally different";

local
  fun advance (FVAR (fv, fbs)) ((bvs, RIGHT tm :: rest), sub) =
    let
      val sub' = fo_raw_match (fv, fbs) (bvs, tm) sub
    in
      ((bvs, rest), sub')
    end
    | advance pat (state as (_, RIGHT _::_), sub) =
    advance pat (tm_pat_break state, sub)
    | advance pat ((bvs, LEFT pat' :: rest), sub) =
    let
      val sub' = pat_fo_match sub pat pat'
    in
      ((tm_pat_correct pat' bvs, rest), sub')
    end
    | advance _ ((_, []), _) =
    raise BUG "discrim_fo_match" "no pats left in list"

  fun finally a ((_, []), sub) =
    SOME (finalize_subst sub, a)
    | finally _ _ = raise BUG "discrim_fo_match" "weird state at end"

  fun tree_match tm =
    tree_partial_trans (fn x => total (advance x))
    finally (([], [RIGHT tm]), empty_raw_subst)
in
  fun discrim_fo_match (DISCRIM (_, d)) tm =
    (flatten o map (tree_match tm)) d
  handle HOL_ERR _ => raise BUG "discrim_fo_match" "should never fail";
end;

(* ------------------------------------------------------------------------- *)
(* Variable Term Discriminators                                              *)
(* Terms come with a list of variables that may be instantiated, the rest    *)
(* should be treated as constants.                                           *)
(* ------------------------------------------------------------------------- *)

type 'a vdiscrim = (vars * 'a) discrim;

val empty_vdiscrim : 'a vdiscrim = empty_discrim;

val vdiscrim_size : 'a vdiscrim -> int = discrim_size;

local
  fun dest (tm : term, (vars : vars, a)) = ((vars, tm), a)
in
  fun dest_vdiscrim d = (map dest o dest_discrim) d;
end;

local
  fun prepare (vars : vars) (tm, a) = (tm, (vars, a))
in
  fun vdiscrim_add ((vars, tm), a) = discrim_add (prepare vars (tm, a));
end;

fun mk_vdiscrim l = trans vdiscrim_add empty_discrim l;

local
  fun vars_check (ho_sub as (sub, _) : ho_substitution, (vars, a)) =
    if subst_vars_in_set sub vars then SOME (ho_sub, a) else NONE
  fun check_ho_match ml = partial_map vars_check ml
in
  fun vdiscrim_ho_match d tm = check_ho_match (discrim_ho_match d tm);
end;

local
  fun vars_check (sub : substitution, (vars, a)) =
    if subst_vars_in_set sub vars then SOME (sub, a) else NONE
  fun check_fo_match ml = partial_map vars_check ml
in
  fun vdiscrim_fo_match d tm = check_fo_match (discrim_fo_match d tm);
end;

(* ------------------------------------------------------------------------- *)
(* Ordered (Variable) Term Discriminators                                    *)
(* Entries are returned in the order they arrived (latest first).            *)
(* ------------------------------------------------------------------------- *)

type 'a ovdiscrim = (int * 'a) vdiscrim;

val empty_ovdiscrim : 'a ovdiscrim = empty_vdiscrim;

val ovdiscrim_size : 'a ovdiscrim -> int = vdiscrim_size;

local
  fun transfer (a, (n : int, b)) = (n, (a, b));
  fun order (m, _) (n, _) = m > n;
  fun dest dl = (map snd o sort order o map transfer) dl;
in
  fun dest_ovdiscrim d = (dest o dest_vdiscrim) d;

  fun ovdiscrim_ho_match ml d = dest (vdiscrim_ho_match ml d)
  handle (h as HOL_ERR _) => raise err_BUG "ovdiscrim_ho_match" h;

  fun ovdiscrim_fo_match ml d = dest (vdiscrim_fo_match ml d)
  handle (h as HOL_ERR _) => raise err_BUG "ovdiscrim_fo_match" h;
end;

fun ovdiscrim_add (tm, a) d = vdiscrim_add (tm, (vdiscrim_size d, a)) d;

fun mk_ovdiscrim l = trans ovdiscrim_add empty_discrim l;

(* non-interactive mode
*)
end;
