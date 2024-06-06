structure ho_basicTools :> ho_basicTools =
struct

open HolKernel Parse boolLib;

open hurdUtils;

infixr 0 ##

val assert = simple_assert;

(* ------------------------------------------------------------------------- *)
(* Debugging.                                                                *)
(* ------------------------------------------------------------------------- *)

val trace_level = ref 0;
val _ = Feedback.register_trace ("ho_basicTools", trace_level, 10);
fun trace l s = if l > !trace_level then () else say (s ^ "\n");
fun trace_x l s f x =
  if l > !trace_level then () else say (s ^ ":\n" ^ f x ^ "\n");
fun trace_CONV l s tm = (trace_x l s term_to_string tm; QCONV ALL_CONV tm);

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
(* Higher-order matching.                                                    *)
(* ------------------------------------------------------------------------- *)

fun dest_ho_pat bvs tm =
  if is_var tm andalso not (is_bv bvs tm) then
    (tm, [])
  else
    let
      val (a, b) = dest_comb tm
      val bi = dest_bv bvs b
    in
      (I ## cons bi) (dest_ho_pat bvs a)
    end;
fun is_ho_pat bvs = can (dest_ho_pat bvs);
fun mk_ho_pat bvs (var, []) = var
  | mk_ho_pat bvs (var, b::bs) =
  mk_comb (mk_ho_pat bvs (var, bs), mk_bv bvs b);

local
  fun beta [] tm = (tm, fn () => REFL tm)
    | beta (v::vs) tm =
    let
      val tm_abs = mk_abs (v, tm)
      val (match_tm, th1) = beta vs tm_abs
    in
      (match_tm,
       fn () =>
       TRANS (MK_COMB (th1 (), REFL v)) (QCONV BETA_CONV (mk_comb (tm_abs, v))))
    end

  fun eta_beta [] tm = (tm, fn () => REFL tm)
    | eta_beta (v::vs) tm =
    let
      val body = eta_conv (mk_abs (v, tm))
      val (match_tm, th) = eta_beta vs body
    in
      (match_tm, fn () => MK_COMB (th (), REFL v))
    end
    handle HOL_ERR _ => beta (v::vs) tm
in
  fun ho_pat_match bvs pat_bvs tm =
    let
      val tm_bvs = filter (is_bv bvs) (free_vars tm)
      val _ = assert (forall (is_bv pat_bvs) tm_bvs)
        (ERR "ho_pat_match" "var pattern doesn't have all bound vars used")
    in
      eta_beta pat_bvs tm
    end

  fun ho_raw_match (var, bs) (bvs, tm) sub =
    let
      val var_bvs = map (mk_bv bvs) bs
    in
      (C (raw_match' var) sub ## I) (ho_pat_match bvs var_bvs tm)
    end
end;

local
  fun check_off_bvs _ tm [] = tm
    | check_off_bvs bvs tm (b :: bs) =
    let
      val (a, v) = dest_comb tm
      val _ = assert (dest_bv bvs v = b) (ERR "fo_pat_match" "wrong bound vars")
    in
      check_off_bvs bvs a bs
    end
in
  fun fo_raw_match (var, bs) (bvs, tm) sub =
    let
      val body = check_off_bvs bvs tm bs
      val bvfvs = listset bvs Isct FVs body
      val _ = assert (HOLset.isEmpty bvfvs)
        (ERR "fo_pat_match" "term to be matched contains bound vars")
    in
      raw_match' var body sub
    end;
end;

local
  fun match (bvs, tm) (bvs', tm') sub =
    if is_bv bvs tm then
      let
        val _ = assert (dest_bv bvs tm = dest_bv bvs' tm')
          (ERR "ho_match" "bound var in pattern does not match")
      in
        (sub, fn () => REFL tm')
      end
    else if is_ho_pat bvs tm then
      ho_raw_match (dest_ho_pat bvs tm) (bvs', tm') sub
    else
      (case Df dest_term (tm, tm') of
         (COMB (Rator, Rand), COMB (Rator', Rand')) =>
         let
           val (sub', rator_th) = match (bvs, Rator) (bvs', Rator') sub
           val (sub'', rand_th) = match (bvs, Rand) (bvs', Rand') sub'
         in
           (sub'', fn () => MK_COMB (rator_th (), rand_th ()))
         end
       | (LAMB (Bvar, Body), LAMB (Bvar', Body')) =>
         let
           val sub' = type_raw_match (type_of Bvar) (type_of Bvar') sub
           val (sub'', thk) = match (Bvar::bvs, Body) (Bvar'::bvs', Body') sub'
         in
           (sub'', fn () => MK_ABS (GEN Bvar' (thk ())))
         end
       | (CONST _, CONST _)
         => (raw_match' tm tm' sub, fn () => REFL tm')
       | (VAR _, _)
         => raise BUG "ho_match" "var in pattern shouldn't be possible"
       | _ => raise ERR "ho_match" "fundamentally different terms")
in
  fun ho_match_bvs (bvs, tm) (bvs', tm') : ho_substitution =
    (finalize_subst ## (fn thk => fn () => SYM (thk ())))
    (match (bvs, tm) (bvs', tm') empty_raw_subst)

  fun ho_match tm tm' : ho_substitution = ho_match_bvs ([], tm) ([], tm')
end;

fun var_ho_match_bvs vars (bvs, tm) (bvs', tm') =
  let
    val ho_sub as (sub, _) = ho_match_bvs (bvs, tm) (bvs', tm')
    val _ = assert (subst_vars_in_set sub vars)
      (ERR "var_ho_match_bvs" "subst vars not contained in set")
  in
    ho_sub
  end;

fun var_ho_match vars tm tm' = var_ho_match_bvs vars ([], tm) ([], tm');

(*
val tm = ``\(x : num). f``;
val tm' = ``\(n : num). T``;
val (sub, th) = try (ho_match tm) tm';

val tm = ``!x y. f x y``;
val tm' = ``!a b. f a a b``;
val (sub, th) = try (ho_match tm) tm';
pinst sub tm;
REWR_CONV (th ()) tm';

val tm = ``!x y z. f x z``;
val tm' = ``!a b c. P (f a c) (g a)``;
val (sub, th) = try (ho_match tm) tm';
pinst sub tm;
REWR_CONV (th ()) tm';

val tm = ``\ (v : 'a). a v (b v)``;
val tm' = ``\ (y : 'a). f y``;
val (sub, th) = try (ho_match tm) tm';
pinst sub tm;
REWR_CONV (th ()) tm';

val tm = ``\ (v : 'a). v``;
val tm' = ``\ (y : 'b). y``;
val (sub, th) = try (ho_match tm) tm';
pinst sub tm;
REWR_CONV (th ()) tm';
*)

(* ------------------------------------------------------------------------- *)
(* Higher-order rewriting.                                                   *)
(* ------------------------------------------------------------------------- *)

(* Normal rewriting *)

fun ho_subst_REWR th (sub, thk) = TRANS (thk ()) (PINST sub th);

fun ho_REWR_CONV th =
  let
    val (vars, th') = thm_to_vthm th
    val pat = LHS th'
  in
    ho_subst_REWR th' o var_ho_match vars pat
  end;

fun ho_REWRITE_CONV ths = QCONV (TOP_DEPTH_CONV (FIRSTC (map ho_REWR_CONV ths)));

fun ho_REWRITE_TAC ths = CONV_TAC (ho_REWRITE_CONV ths);

(* Conditional rewriting, pass in a prover *)

fun ho_subst_COND_REWR th =
  let
    val (cond, _) = (dest_imp o concl) th
  in
    fn prover => fn (sub, thk) =>
    let
      val goal = pinst sub cond
      val _ = trace_x 2 "ho_subst_COND_REWR: goal" term_to_string goal
      val proved_cond = prover goal
    in
      TRANS (thk ()) (MP (PINST sub th) proved_cond)
      handle h as HOL_ERR _ => raise err_BUG
        ("ho_subst_COND_REWR: using crw\n" ^ thm_to_string th ^
         "\nand proved_cond\n" ^ thm_to_string proved_cond) h
    end
  end;

fun ho_COND_REWR_CONV th =
  let
    val (vars, th') = thm_to_vthm th
    val pat = (lhs o snd o dest_imp o concl) th'
    val f = ho_subst_COND_REWR th'
  in
    fn prover => f prover o var_ho_match vars pat
  end;

(* non-interactive mode
*)
end;
