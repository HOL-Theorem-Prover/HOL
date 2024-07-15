structure skiTools :> skiTools =
struct

open HolKernel Parse boolLib;

open hurdUtils ho_basicTools unifyTools skiTheory;

infixr 0 oo ## ++ << || THENC ORELSEC THENR ORELSER;
infix 1 >> |->;

val op++ = op THEN;
val op<< = op THENL;
val op|| = op ORELSE;
val op>> = op THEN1;
val !! = REPEAT;

fun trace _ _ = ();
fun printVal _ = ();

val assert = simple_assert;

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
(* Conversion to combinators {S,K,I}.                                        *)
(* ------------------------------------------------------------------------- *)

fun SKI_CONV tm =
  (case dest_term tm of
     CONST _ => ALL_CONV
   | VAR _ => ALL_CONV
   | COMB _ => RAND_CONV SKI_CONV THENC RATOR_CONV SKI_CONV
   | LAMB _
     => ABS_CONV SKI_CONV THENC
        (ho_REWR_CONV MK_K ORELSEC
         ho_REWR_CONV MK_I ORELSEC
         ho_REWR_CONV MK_S) THENC
        SKI_CONV) tm;

(*
try SKI_CONV ``?x. !y. x y = y + 1``;
SKI_CONV ``\x. f x o g``;
SKI_CONV ``\x y. f x y``;
SKI_CONV ``$? = \P. P ($@ P)``;
SKI_CONV ``$==> = \a b. ~a \/ b``;
SKI_CONV ``$! = \P. K T = P``;
SKI_CONV ``!x y. P x y``;
SKI_CONV ``!x y. P y x``;
SKI_CONV ``(P = Q) = (!x. P x = Q x)``;
*)

(* ------------------------------------------------------------------------- *)
(* A combinator {S,K,I} unify function.                                      *)
(* ------------------------------------------------------------------------- *)

local
  fun occurs v tm = free_in v tm

  fun solve _ sub [] = sub
    | solve vars sub (current :: next) =
    solve' vars sub (Df (pinst sub) current) next
  and solve' vars sub (tm1, tm2) rest =
    if is_tmvar vars tm1 then
      if tm1 ~~ tm2 then solve vars sub rest
      else if occurs tm1 tm2 then raise ERR "ski_unify" "occurs check"
      else
        (case total (tfind_redex tm1) (fst sub) of SOME {residue, ...}
           => solve' vars sub (tm2, residue) rest
         | NONE =>
           let
             val (ty1, ty2) = Df type_of (tm1, tm2)
             val sub_extra = var_type_unify (snd vars) ty1 ty2
             val (tm1', tm2') = Df (inst_ty sub_extra) (tm1, tm2)
             val sub' = refine_subst sub ([tm1' |-> tm2'], sub_extra)
             val vars' = (map (inst_ty sub_extra) ## I) vars
           in
             solve vars' sub' rest
           end)
    else if is_tmvar vars tm2 then solve' vars sub (tm2, tm1) rest
    else
      (case Df dest_term (tm1, tm2) of
         (COMB (Rator, Rand), COMB (Rator', Rand'))
         => solve' vars sub (Rator, Rator') ((Rand, Rand') :: rest)
       | (VAR (Name, Ty), VAR (Name', Ty')) =>
         let
           val _ = assert (Name = Name') (ERR "ski_unify" "different vars")
           val _ = assert (Ty = Ty')
                          (BUG "ski_unify" "same var, different types?")
         in
           solve vars sub rest
         end
       | (CONST {Name, Thy, Ty}, CONST {Name = Name', Thy = Thy', Ty = Ty'}) =>
         let
           val _ =
             assert (Name = Name' andalso Thy = Thy')
                    (ERR "ski_unify" "different vars")
           val sub_extra = var_type_unify (snd vars) Ty Ty'
           val sub' = refine_subst sub ([], sub_extra)
           val vars' = (map (inst_ty sub_extra) ## I) vars
         in
           solve vars' sub' rest
         end
       | _ => raise ERR "ski_unify" "terms fundamentally different")
in
  fun ski_unifyl vars work = solve vars empty_subst work;
  fun ski_unify vars tm1 tm2 = solve' vars empty_subst (tm1, tm2) [];
end;

(* ------------------------------------------------------------------------- *)
(* A combinator {S,K,I} term discriminator.                                  *)
(* ------------------------------------------------------------------------- *)

datatype ski_pattern
  = SKI_COMB_BEGIN
  | SKI_COMB_END
  | SKI_CONST of term
  | SKI_VAR of term;

datatype 'a ski_discrim =
  SKI_DISCRIM of int * (ski_pattern, vars * 'a) tree list;

fun skipat_eq p1 p2 =
  case (p1, p2) of
      (SKI_COMB_BEGIN, SKI_COMB_BEGIN) => true
    | (SKI_COMB_END, SKI_COMB_END) => true
    | (SKI_CONST t1, SKI_CONST t2) => aconv t1 t2
    | (SKI_VAR t1, SKI_VAR t2) => aconv t1 t2
    | _ => false

val empty_ski_discrim = SKI_DISCRIM (0, []);
fun ski_discrim_size (SKI_DISCRIM (i, _)) = i;

fun ski_pattern_term_build SKI_COMB_BEGIN stack =
  (LEFT SKI_COMB_BEGIN :: stack)
  | ski_pattern_term_build SKI_COMB_END
  (RIGHT rand :: RIGHT rator :: LEFT SKI_COMB_BEGIN :: stack) =
  (RIGHT (mk_comb (rator, rand)) :: stack)
  | ski_pattern_term_build (SKI_CONST c) stack = RIGHT c :: stack
  | ski_pattern_term_build (SKI_VAR v) stack = RIGHT v :: stack
  | ski_pattern_term_build SKI_COMB_END _ =
  raise BUG "ski_pattern_term_build" "badly formed list";

local
  fun final [RIGHT tm] = tm
    | final _ = raise ERR "ski_patterns_to_term" "not a complete pattern list"

  fun final_a (vars, a) stack = ((vars, final stack), a)
in
  fun ski_patterns_to_term pats =
    final (trans ski_pattern_term_build [] pats)

  fun dest_ski_discrim (SKI_DISCRIM (_, d)) =
    flatten (map (tree_trans ski_pattern_term_build final_a []) d)
end;

fun ski_pattern_term_break ((tm_vars, _) : vars) (RIGHT tm :: rest) =
  (case dest_term tm of COMB (Rator, Rand) =>
     LEFT SKI_COMB_BEGIN :: RIGHT Rator :: RIGHT Rand ::
     LEFT SKI_COMB_END :: rest
   | LAMB _ => raise BUG "ski_pattern_term_break" "can't break a lambda"
   | _ => LEFT (if tmem tm tm_vars then SKI_VAR tm else SKI_CONST tm) :: rest)
  | ski_pattern_term_break _ [] =
  raise BUG "ski_pattern_term_break" "nothing to break"
  | ski_pattern_term_break _ (LEFT _ :: _) =
  raise BUG "ski_pattern_term_break" "can't break a ski_pattern";

fun vterm_to_ski_patterns (vars, tm) =
  let
    fun break res [] = rev res
      | break res (LEFT p :: rest) = break (p :: res) rest
      | break res ripe = break res (ski_pattern_term_break vars ripe)
    val res = break [] [RIGHT tm]
    val _ =
      trace "vterm_to_ski_patterns: ((vars, tm), res)"
      (fn () => printVal ((vars, tm), res))
  in
    res
  end;

local
  fun add a [] leaves = LEAF a :: leaves
    | add a (pat :: next) [] = [BRANCH (pat, add a next [])]
    | add a (pats as pat :: next) ((b as BRANCH (pat', trees)) :: branches) =
    if skipat_eq pat pat' then BRANCH (pat', add a next trees) :: branches
    else b :: add a pats branches
    | add _ (_::_) (LEAF _::_) =
    raise BUG "discrim_add" "expected a branch, got a leaf"
in
  fun ski_discrim_add ((vars, tm), a) (SKI_DISCRIM (i, d)) =
    SKI_DISCRIM (i + 1, add (vars, a) (vterm_to_ski_patterns (vars, tm)) d)
end;

fun ski_discrim_addl l d = trans ski_discrim_add d l;

fun mk_ski_discrim l = ski_discrim_addl l empty_ski_discrim;

fun ski_pattern_reduce (SKI_VAR _) _ _ =
  raise BUG "ski_pattern_reduce" "can't reduce variables"
  | ski_pattern_reduce SKI_COMB_BEGIN SKI_COMB_BEGIN sub = sub
  | ski_pattern_reduce SKI_COMB_END SKI_COMB_END sub = sub
  | ski_pattern_reduce (SKI_CONST c) (SKI_CONST c') sub =
  raw_match' c c' sub
  | ski_pattern_reduce _ _ _ =
  raise ERR "ski_pattern_reduce" "patterns fundamentally different";

local
  fun advance (SKI_VAR v) (RIGHT tm :: rest, sub) = (rest, raw_match' v tm sub)
    | advance pat (state as RIGHT _ :: _, sub) =
    advance pat (ski_pattern_term_break empty_vars state, sub)
    | advance pat (LEFT pat' :: rest, sub) =
    (rest, ski_pattern_reduce pat pat' sub)
    | advance _ ([], _) =
    raise BUG "ski_discrim_match" "no patterns left in list"

  fun finally (_, a) ([], sub) = SOME (finalize_subst sub, a)
    | finally _ _ = raise BUG "ski_discrim_match" "patterns left at end"

  fun tree_match tm =
    tree_partial_trans (total o advance) finally ([RIGHT tm], empty_raw_subst)
in
  fun ski_discrim_match (SKI_DISCRIM (_, d)) tm =
    (flatten o map (tree_match tm)) d
  handle HOL_ERR _ => raise BUG "ski_discrim_match" "should never fail";
end;

local
  fun advance _ pat (SOME (v, lstate), rstate, work) =
    (case ski_pattern_term_build pat lstate of
         [RIGHT tm] => (NONE, rstate, (v, tm) :: work)
       | lstate' => (SOME (v, lstate'), rstate, work))
    | advance _ (SKI_VAR v) (NONE, RIGHT tm :: rest, work) =
        (NONE, rest, (v, tm) :: work)
    | advance vars pat (NONE, rstate as RIGHT _ :: _, work) =
        advance vars pat (NONE, ski_pattern_term_break vars rstate, work)
    | advance vars pat (NONE, LEFT (SKI_VAR v) :: rest, work) =
        advance vars pat (SOME (v, []), rest, work)
    | advance _ (SKI_CONST c) (NONE, LEFT (SKI_CONST c') :: rest, work) =
        (NONE, rest, (c, c') :: work)
    | advance _ pat (NONE, LEFT pat' :: rest, work) =
        if skipat_eq pat pat' then (NONE, rest, work)
        else raise ERR "ski_discrim_unify" "terms fundamentally different"
    | advance _ _ (NONE, [], _) =
        raise BUG "ski_discrim_match" "no patterns left in list";

  fun finally (vars, a) (NONE, [], work) = SOME ((vars, work), a)
    | finally _ _ = raise BUG "ski_discrim_unify" "patterns left at end";

  fun tree_search vars tm =
    tree_partial_trans (total o advance vars) finally (NONE, [RIGHT tm], []);
in
  fun ski_discrim_unify (sd as SKI_DISCRIM (_, d)) (vars, tm) =
    let
      val shortlist = (flatten o map (tree_search vars tm)) d
      fun select ((vars', work), a) =
        (ski_unifyl (vars_union vars vars') work, a)
      val res = partial_map (total select) shortlist
      val _ = trace
        "ski_discrim_unify: ((vars, tm), map fst res)"
        (fn () => printVal ((vars, tm), map fst res))
    in
      res
    end
end;

(* non-interactive mode
*)
end;
