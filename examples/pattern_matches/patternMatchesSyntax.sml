structure patternMatchesSyntax :> patternMatchesSyntax =
struct

open HolKernel Parse boolLib bossLib
open patternMatchesTheory
open pairSyntax
open ConseqConv


(***********************************************)
(* Auxiliary stuff                             *)
(***********************************************)

(* Stolen from pairTools. TODO:
   add it to interface there. *)
fun variant_of_term vs t =
let
   val check_vars = free_vars t;
   val (_,sub) =
      foldl (fn (v, (vs,sub)) =>
	  let
             val v' = variant vs v;
             val vs' = v'::vs;
             val sub' = if (aconv v v') then sub else
			(v |-> v')::sub;
          in
             (vs',sub')
          end) (vs,[]) check_vars;
  val t' = subst sub t
in
  (t', sub)
end;

fun varname_starts_with_uscore v = let
  val (s, _) = dest_var v
in
  String.sub(s, 0) = #"_"
end handle HOL_ERR _ => false


fun mk_var_gen prefix avoid = let
  val c = ref 0
  val avoidL = List.map (fst o dest_var) avoid
  fun next_name () = let
    val vn = prefix ^ (int_to_string (!c))
    val _ = c := !c + 1
    val ok = not (mem vn avoidL)
  in
    if ok then vn else next_name ()
  end
in
  fn ty => mk_var (next_name (), ty)
end

fun mk_wildcard_gen avoid = mk_var_gen "_" avoid


(* Get the first element of l that satisfies p and
   remove it from the list.. *)
fun pick_element p l = let
 fun aux acc l =
   case l of
       [] => failwith "no element found"
     | e::l => (if p e then (e, List.rev acc @ l)
                else aux (e::acc) l)
 in
   aux [] l
 end

(* strip_comb with a maximum number of splits *)
fun strip_comb_bounded_aux acc n t = if (n > 0) then (let
  val (t', a) = dest_comb t
  in
  strip_comb_bounded_aux (a::acc) (n - 1) t'
end handle HOL_ERR _ => (t, acc)) else (t, acc)

fun strip_comb_bounded n t = strip_comb_bounded_aux [] n t

(* apply a conversion to all leafs of a disjunct *)
fun ALL_DISJ_CONV c t = if (is_disj t) then (
  (BINOP_CONV (ALL_DISJ_CONV c)) t
) else (TRY_CONV c) t

(* apply a conversion to all leafs of a disjunct
   and simplify the result by removing T and F. *)
fun ALL_DISJ_TF_ELIM_CONV c t = let
  val (t1, t2) = dest_disj t
in
  if (aconv t1 T) then
    SPEC t2 (ConseqConvTheory.OR_CLAUSES_TX)
  else if (aconv t2 T) then
    SPEC t1 (ConseqConvTheory.OR_CLAUSES_XT)
  else let
    val thm1_opt = SOME (ALL_DISJ_TF_ELIM_CONV c t1) handle UNCHANGED => NONE
    val thm1_opt_eq_T = case thm1_opt of
        NONE => false
      | SOME thm1 => (aconv (rhs (concl thm1)) T)
    val thm2_opt = if thm1_opt_eq_T then NONE else SOME (ALL_DISJ_TF_ELIM_CONV c t2) handle UNCHANGED => NONE

    val thm0 = case (thm1_opt, thm2_opt) of
        (NONE, NONE) => raise UNCHANGED
      | (SOME thm1, NONE) => RATOR_CONV (RAND_CONV (K thm1)) t
      | (NONE, SOME thm2) => RAND_CONV (K thm2) t
      | (SOME thm1, SOME thm2) => (
           (RATOR_CONV (RAND_CONV (K thm1))) THENC
           (RAND_CONV (K thm2))) t

    val (t1', t2') = dest_disj (rhs (concl thm0))

    val rewr_thm_opt = if (aconv t1' T) then
        SOME (ConseqConvTheory.OR_CLAUSES_TX)
      else if (aconv t1' F) then
        SOME (ConseqConvTheory.OR_CLAUSES_FX)
      else if (aconv t2' T) then
        SOME (ConseqConvTheory.OR_CLAUSES_XT)
      else if (aconv t2' F) then
        SOME (ConseqConvTheory.OR_CLAUSES_XF)
      else NONE

   val thm1 = case rewr_thm_opt of
      NONE => thm0
    | SOME thm_rw => RIGHT_CONV_RULE (REWR_CONV thm_rw) thm0
  in
    thm1
  end
end handle HOL_ERR _ => (TRY_CONV c) t


(* apply a conversion to all leafs of a conjunct. *)
fun ALL_CONJ_CONV c t = if (is_conj t) then (
  (BINOP_CONV (ALL_CONJ_CONV c)) t
) else (TRY_CONV c) t


fun DECEND_CONV c_desc c t =
  (c THENC TRY_CONV (c_desc (DECEND_CONV c_desc c))) t


fun STRIP_ABS_CONV conv t =
  if (is_abs t) then ABS_CONV (STRIP_ABS_CONV conv) t else
  conv t

fun has_subterm p t = ((find_term p t; true) handle HOL_ERR _ => false)

(* like proof, but less verbose, since we expect that it might fail *)
val prove_attempt = Lib.with_flag (Feedback.emit_MESG, false) prove


(***********************************************)
(* Labels from markerLib                       *)
(***********************************************)

(* generating fresh labels and vars using
   a counter *)
fun mk_new_label_gen prefix = let
  val c = ref 0
in
  fn () => let
    val l = prefix ^ int_to_string (!c)
    val _ = c := !c + 1
  in
     l
  end
end

fun add_labels_CONV lbls t = let
  val lbl_tm = List.foldl markerSyntax.mk_label t lbls
in
  GSYM ((REPEATC markerLib.DEST_LABEL_CONV) lbl_tm)
end

(*
  val mk_new_label = mk_new_label_generator "disj"
  val lbl_tm = markerSyntax.mk_label (mk_new_label (), lbl_tm)
  val t = lbl_tm
*)

fun strip_labels t = let
  fun aux acc t = let
    val (l, t') = markerSyntax.dest_label t
  in
    aux (l::acc) t'
  end handle HOL_ERR _ => (List.rev acc, t)
in
  aux [] t
end

(* conversion underneath a list of labels *)
fun strip_labels_CONV c t =
  if (markerSyntax.is_label t) then
    RAND_CONV (strip_labels_CONV c) t
  else
    c t

(* conversion underneath a list of labels containing at least
   one label from list [lbls]. *)
fun guarded_strip_labels_CONV lbls c t = let
  val (lbls_found, _) = strip_labels t
  val found = List.exists (fn l1 => List.exists (fn l2 => (l1 = l2)) lbls) lbls_found
in
  if not found then raise UNCHANGED else
     strip_labels_CONV c t
end


(***********************************************)
(* Terms                                       *)
(***********************************************)

val ty_var_subst = [alpha |-> gen_tyvar (),
             beta |-> gen_tyvar (),
             gamma |-> gen_tyvar (),
             delta |-> gen_tyvar (),
             ``:'e`` |-> gen_tyvar (),
             ``:'f`` |-> gen_tyvar (),
             ``:'g`` |-> gen_tyvar (),
             ``:'h`` |-> gen_tyvar (),
             ``:'i`` |-> gen_tyvar (),
             ``:'j`` |-> gen_tyvar ()
            ]

val PMATCH_ROW_tm = ``PMATCH_ROW``
val PMATCH_ROW_gtm = inst ty_var_subst PMATCH_ROW_tm;

val PMATCH_ROW_COND_tm = ``PMATCH_ROW_COND``
val PMATCH_ROW_COND_gtm = inst ty_var_subst PMATCH_ROW_COND_tm;

val PMATCH_ROW_COND_EX_tm = ``PMATCH_ROW_COND_EX``
val PMATCH_ROW_COND_EX_gtm = inst ty_var_subst PMATCH_ROW_COND_EX_tm;

val PMATCH_tm = ``PMATCH``
val PMATCH_gtm = inst ty_var_subst PMATCH_tm

fun FRESH_TY_VARS_RULE thm =
  INST_TYPE ty_var_subst thm

fun REMOVE_REBIND_CONV_AUX avoid t = let
  val (v, t') = dest_abs t
  val v' = variant avoid v
  val t'' = subst [v |-> v'] t'
  val (t''', avoid') = REMOVE_REBIND_CONV_AUX (v'::avoid) t''
in
  (mk_abs (v', t'''), avoid')
end handle HOL_ERR _ => let
  val (t1, t2) = dest_comb t
  val (t1', avoid1) = REMOVE_REBIND_CONV_AUX avoid t1
  val (t2', avoid2) = REMOVE_REBIND_CONV_AUX avoid1 t2
in
  (mk_comb (t1', t2'), avoid2)
end handle HOL_ERR _ => (t, avoid)

fun REMOVE_REBIND_CONV t = let
  val (t', _) = REMOVE_REBIND_CONV_AUX [] t
in
  ALPHA t t'
end


(***********************************************)
(* PMATCH_ROW                                  *)
(***********************************************)

fun dest_PMATCH_ROW row = let
  val (f, args) = strip_comb row
  val _ = if (same_const f PMATCH_ROW_tm) andalso (List.length args = 3) then () else failwith "dest_PMATCH_ROW"
in
  (el 1 args, el 2 args, el 3 args)
end

fun is_PMATCH_ROW t = can dest_PMATCH_ROW t

fun mk_PMATCH_ROW (p_t, g_t, r_t) =
  list_mk_icomb (PMATCH_ROW_gtm, [p_t, g_t, r_t])

fun mk_pabs_from_vars vars tl = case vars of
      []  => let
               val uv = variant (free_varsl tl) ``uv:unit``
             in
               fn t => mk_abs (uv, t)
             end
    | [v] => (fn t => mk_abs (v, t))
    | _   => (fn t => pairSyntax.mk_pabs (pairSyntax.list_mk_pair vars, t))

fun mk_PMATCH_ROW_PABS vars (p_t, g_t, r_t) = let
    val mk_pabs = mk_pabs_from_vars vars [p_t, g_t, r_t]
  in
    mk_PMATCH_ROW (mk_pabs p_t, mk_pabs g_t, mk_pabs r_t)
  end


fun mk_PMATCH_ROW_PABS_WILDCARDS vars (p_t, g_t, r_t) = let
    val gr_s = FVL [g_t, r_t] empty_tmset
    val p_s = FVL [p_t] empty_tmset

    val mk_wc = mk_wildcard_gen (HOLset.listItems
      (HOLset.union (gr_s, p_s)))

    fun apply (v, (vars', subst)) = (
      if (not (HOLset.member (gr_s, v)) andalso
          not (varname_starts_with_uscore v)) then let
        val v' = mk_wc (type_of v)
      in
        (v'::vars', (v |-> v')::subst)
      end else
         (v::vars', subst)
    )

    val (vars'_rev, subst) = List.foldl apply ([], []) vars
    val vars' = List.rev vars'_rev
    val p_t' = Term.subst subst p_t
    val use_wc = not (List.null subst)
  in
    (use_wc, mk_PMATCH_ROW_PABS vars' (p_t', g_t, r_t))
  end


fun dest_PMATCH_ROW_ABS row = let
  val (p_t, g_t, r_t) = dest_PMATCH_ROW row

  val (p_vars, p_body) = pairSyntax.dest_pabs p_t
  val (g_vars, g_body) = pairSyntax.dest_pabs g_t
  val (r_vars, r_body) = pairSyntax.dest_pabs r_t

  val _ = if (aconv p_vars g_vars) andalso (aconv g_vars r_vars) then
    () else failwith "dest_PMATCH_ROW_ABS"
in
  (p_vars, p_body, g_body, r_body)
end


fun dest_PMATCH_ROW_ABS_VARIANT vs row = let
  val (p_vars, p_body, g_body, r_body) = dest_PMATCH_ROW_ABS row
  val (p_vars', sub) = variant_of_term vs p_vars
in
  (p_vars', subst sub p_body, subst sub g_body, subst sub r_body)
end;

val K_elim = prove (``K x = (\y. x)``, SIMP_TAC std_ss [
  combinTheory.K_DEF])

fun PMATCH_ROW_PABS_ELIM_CONV row = let
  val (p, _, _) = dest_PMATCH_ROW row
  val (vars, _) = pairSyntax.dest_pabs p

  val c = TRY_CONV (REWR_CONV K_elim) THENC (TRY_CONV pairTools.PABS_ELIM_CONV)

  val thm = ((RAND_CONV c) THENC
             (RATOR_CONV (RAND_CONV c)) THENC
             (RATOR_CONV (RATOR_CONV (RAND_CONV c)))) row
            handle UNCHANGED => REFL row
in
  (vars, thm)
end;


fun PMATCH_ROW_PABS_INTRO_CONV vars row = let
  val _ = if (is_PMATCH_ROW row) then () else failwith "PMATCH_ROW_PABS_INTRO_CONV"

  val (vars', _) = variant_of_term (free_vars row) vars
  val c = pairTools.PABS_INTRO_CONV vars'
  val thm = ((RAND_CONV c) THENC
             (RATOR_CONV (RAND_CONV c)) THENC
             (RATOR_CONV (RATOR_CONV (RAND_CONV c)))) row
in
  thm
end;

fun PMATCH_ROW_FORCE_SAME_VARS_CONV row = let
  val _ = if not (is_PMATCH_ROW row) then raise UNCHANGED else ()
  val _ = if can dest_PMATCH_ROW_ABS row then raise UNCHANGED else ()
  val (vars, thm0) = PMATCH_ROW_PABS_ELIM_CONV row
  val thm1 = PMATCH_ROW_PABS_INTRO_CONV vars (rhs (concl thm0))
in
  TRANS thm0 thm1
end handle HOL_ERR _ => raise UNCHANGED


fun PMATCH_ROW_INTRO_WILDCARDS_CONV row = let
  val (vars_tm, p_t, g_t, r_t) = dest_PMATCH_ROW_ABS row
  val vars = pairSyntax.strip_pair vars_tm
  val (ch, row') = mk_PMATCH_ROW_PABS_WILDCARDS vars (p_t, g_t, r_t)
  val _ = if ch then () else raise UNCHANGED
in
  ALPHA row row'
end handle HOL_ERR _ => raise UNCHANGED

(*
val row = ``
      PMATCH_ROW (\ (y,z). (SOME y,SUC z,[1; 2]))
                 (\ x. T)
                 (\ (y,z). y + z)``

val (vars, thm) = PMATCH_ROW_PABS_ELIM_CONV row
val thm2 = PMATCH_ROW_PABS_INTRO_CONV vars (rhs (concl thm))
val row = rhs (concl thm2)
*)

(***********************************************)
(* PMATCH                                      *)
(***********************************************)

fun mk_PMATCH v rows = let
  val rows_ty = let
    val ty0 = type_of PMATCH_tm
    val (arg_tys, _) = wfrecUtils.strip_fun_type  ty0
  in el 2 arg_tys end

  val ty_subst = match_type rows_ty (type_of rows)
  val b_tm = inst ty_subst PMATCH_tm
  val t1 = mk_comb (b_tm, v)
  val t2 = mk_comb (t1, rows)
in
  t2
end

fun dest_PMATCH t = let
  val (f, args) = strip_comb t
  val _ = if (same_const f PMATCH_tm) andalso (List.length args = 2) then () else failwith "dest_PMATCH"
  val (l, _) = listSyntax.dest_list (el 2 args)
in
  (el 1 args, l)
end

fun is_PMATCH t = can dest_PMATCH t

fun dest_PATLIST_COLS v ps = let
  fun split_pat p = let
    val (vars_tm, pt) = pairSyntax.dest_pabs p
    val vars = pairSyntax.strip_pair vars_tm
    val pts = pairSyntax.strip_pair pt
  in
    List.map (fn x => (vars, x)) pts
  end
  val rows' = map split_pat ps

  val col_no = length (hd rows')
  fun aux acc v col_no = if (col_no <= 1) then List.rev (v::acc) else (
    let
       val (v1, v2) = pairSyntax.dest_pair v handle HOL_ERR _ =>
          (pairSyntax.mk_fst v,  pairSyntax.mk_snd v)
    in
       aux (v1::acc) v2 (col_no-1)
    end
  )

  val vs = aux [] v col_no

  fun get_cols acc vs rows = case vs of
      [] => List.rev acc
    | (v::vs') => let
        val col = map hd rows
        val rows' = map tl rows
      in
        get_cols ((v, col)::acc) vs' rows'
      end
  val cols = get_cols [] vs rows'
in
  cols
end handle Empty => failwith "dest_PATLIST_COLS"


fun dest_PMATCH_COLS t = let
  val (v, rows) = dest_PMATCH t
  val ps = List.map (#1 o dest_PMATCH_ROW) rows
in
  dest_PATLIST_COLS v ps
end

fun list_CONV c t =
  if not (listSyntax.is_cons t) then  raise UNCHANGED else (
  (RATOR_CONV (RAND_CONV c) THENC
   RAND_CONV (list_CONV c)) t)

fun list_nth_CONV n c t =
  if not (listSyntax.is_cons t) then  raise UNCHANGED else
  if (n < 0) then raise UNCHANGED else
  if (n = 0) then RATOR_CONV (RAND_CONV c) t else
  (RAND_CONV (list_nth_CONV (n-1) c)) t

fun PMATCH_ROWS_CONV c t = let
  val _ = if not (is_PMATCH t) then raise UNCHANGED else ()
in
  RAND_CONV (list_CONV c) t
end

val PMATCH_FORCE_SAME_VARS_CONV =
  PMATCH_ROWS_CONV PMATCH_ROW_FORCE_SAME_VARS_CONV

val PMATCH_INTRO_WILDCARDS_CONV =
  PMATCH_ROWS_CONV PMATCH_ROW_INTRO_WILDCARDS_CONV


(***********************************************)
(* PMATCH_ROW_COND                             *)
(***********************************************)

fun dest_PMATCH_ROW_COND rc = let
  val (f, args) = strip_comb rc
  val _ = if (same_const f PMATCH_ROW_COND_tm) andalso (List.length args = 4) then () else failwith "dest_PMATCH_ROW_COND"
in
  (el 1 args, el 2 args, el 3 args, el 4 args)
end

fun is_PMATCH_ROW_COND t = can dest_PMATCH_ROW_COND t

fun mk_PMATCH_ROW_COND (p_t, g_t, i, x) =
  list_mk_icomb (PMATCH_ROW_COND_gtm, [p_t, g_t, i, x])

fun mk_PMATCH_ROW_COND_PABS vars (p_t, g_t, i, x) = let
    val mk_pabs = mk_pabs_from_vars vars [p_t, g_t, x]
  in
    mk_PMATCH_ROW_COND (mk_pabs p_t, mk_pabs g_t, i, x)
  end

fun dest_PMATCH_ROW_COND_ABS rc = let
  val (p_t, g_t, i_t, x_t) = dest_PMATCH_ROW_COND rc

  val (p_vars, p_body) = pairSyntax.dest_pabs p_t
  val (g_vars, g_body) = pairSyntax.dest_pabs g_t

  val _ = if (aconv p_vars g_vars) then
    () else failwith "dest_PMATCH_ROW_COND_ABS"
in
  (p_vars, p_body, g_body, i_t, x_t)
end


(***********************************************)
(* PMATCH_ROW_COND_EX                          *)
(***********************************************)

fun dest_PMATCH_ROW_COND_EX rc = let
  val (f, args) = strip_comb rc
  val _ = if (same_const f PMATCH_ROW_COND_EX_tm) andalso (List.length args = 3) then () else failwith "dest_PMATCH_ROW_COND_EX"
in
  (el 1 args, el 2 args, el 3 args)
end

fun is_PMATCH_ROW_COND_EX t = can dest_PMATCH_ROW_COND_EX t

fun mk_PMATCH_ROW_COND_EX (i, p_t, g_t) =
  list_mk_icomb (PMATCH_ROW_COND_EX_gtm, [i, p_t, g_t])

fun mk_PMATCH_ROW_COND_EX_PABS vars (i, p_t, g_t) = let
    val mk_pabs = mk_pabs_from_vars vars [p_t, g_t]
  in
    mk_PMATCH_ROW_COND_EX (i, mk_pabs p_t, mk_pabs g_t)
  end

fun mk_PMATCH_ROW_COND_EX_PABS_MOVE_TO_GUARDS find vars (i, p_t, g_t) = let
  val fr_vs = free_vars i @ free_vars p_t @ free_vars g_t
  fun move_to_guard (vars, p_t, g_t) = let
    val (p: term) = case find vars p_t of
                NONE => failwith "not found"
              | SOME p => p
    val _ = if (mem p vars) then failwith "loop" else ()
    val x = mk_var ("x", type_of p)
    val x = variant (fr_vs @ vars) x
    val p_t' = Term.subst [p |-> x] p_t
    val g_t' = mk_conj (mk_eq (x, p), g_t)
    val vars' = x :: vars
  in
    move_to_guard (vars', p_t', g_t')
  end handle HOL_ERR _ => (vars, p_t, g_t)

  val (vars', p_t', g_t') = move_to_guard (vars, p_t, g_t)
in
  mk_PMATCH_ROW_COND_EX_PABS vars' (i, p_t', g_t')
end


fun mk_PMATCH_ROW_COND_EX_pat i p = let
    val (vars, _) = pairSyntax.dest_pabs p
    val g = pairSyntax.mk_pabs (vars, T)
  in
    mk_PMATCH_ROW_COND_EX (i, p, g)
  end

fun mk_PMATCH_ROW_COND_EX_ROW i r = let
    val (p, g, _) = dest_PMATCH_ROW r
  in
    mk_PMATCH_ROW_COND_EX (i, p, g)
  end

fun dest_PMATCH_ROW_COND_EX_ABS rc = let
  val (i_t, p_t, g_t) = dest_PMATCH_ROW_COND_EX rc

  val (p_vars, p_body) = pairSyntax.dest_pabs p_t
  val (g_vars, g_body) = pairSyntax.dest_pabs g_t

  val _ = if (aconv p_vars g_vars) then
    () else failwith "dest_PMATCH_ROW_COND_EX_ABS"
in
  (i_t, p_vars, p_body, g_body)
end


(*
val t = (el 4 o strip_disj o snd o strip_forall o concl) thm
val v = (fst o dest_forall o concl) thm
val t = ``x = (NONE,c)``
val v = lhs t
fun P vs x = NONE
*)

fun PMATCH_ROW_COND_EX_INTRO_CONV_GEN P v t = let
  val (vs, b) = strip_exists t
  val b_conjs = strip_conj b
  val (peq_t, guards) = pick_element (fn c => (aconv (lhs c) v handle HOL_ERR _ => false)) b_conjs

  val p_t = rhs peq_t
  val g_t = if List.null guards then T else list_mk_conj guards

  val rc = mk_PMATCH_ROW_COND_EX_PABS vs (v, p_t, g_t)

  val rc_eq_tm = mk_eq (t, rc)
  (* set_goal ([], rc_eq_tm) *)
  val rc_eq_thm = prove (rc_eq_tm,
    SIMP_TAC std_ss [PMATCH_ROW_COND_EX_def, PMATCH_ROW_COND_def, pairTheory.EXISTS_PROD] THEN
    TRY (REDEPTH_CONSEQ_CONV_TAC (K EXISTS_EQ___CONSEQ_CONV)) THEN
    SIMP_TAC (std_ss++boolSimps.EQUIV_EXTRACT_ss) []
  )
in
  rc_eq_thm
end

fun PMATCH_ROW_COND_EX_INTRO_CONV v t =
  PMATCH_ROW_COND_EX_INTRO_CONV_GEN (fn _ => fn _ => NONE) v t;

fun nchotomy2PMATCH_ROW_COND_EX_CONV_GEN P t = let
  val (v, _) = dest_forall t
in
  (QUANT_CONV (ALL_DISJ_CONV (PMATCH_ROW_COND_EX_INTRO_CONV_GEN P v))) t
end;

fun nchotomy2PMATCH_ROW_COND_EX_CONV t =
  nchotomy2PMATCH_ROW_COND_EX_CONV_GEN (fn _ => fn _ => NONE) t;

fun PMATCH_ROW_COND_EX_ELIM_CONV t = let
  val (_, p_t, _) = dest_PMATCH_ROW_COND_EX t
  val (vars, _) = pairSyntax.dest_pabs p_t

  val thm0 = REWR_CONV PMATCH_ROW_COND_EX_FULL_DEF t
  val thm1 = RIGHT_CONV_RULE (RAND_CONV (pairTools.PABS_INTRO_CONV vars)) thm0
  val thm2 = RIGHT_CONV_RULE pairTools.ELIM_TUPLED_QUANT_CONV thm1 handle HOL_ERR _ => thm1
  val thm3 = RIGHT_CONV_RULE (STRIP_QUANT_CONV (DEPTH_CONV pairLib.GEN_BETA_CONV)) thm2
  val thm4 = RIGHT_CONV_RULE (PURE_REWRITE_CONV [AND_CLAUSES]) thm3
  val thm5 = RIGHT_CONV_RULE (REWR_CONV boolTheory.EXISTS_SIMP) thm4 handle HOL_ERR _ => thm4
in
  thm5
end


(***********************************************)
(* Pretty Printing                             *)
(***********************************************)

val use_pmatch_pp = ref true
val _ = Feedback.register_btrace ("use pmatch_pp", use_pmatch_pp);

fun pmatch_printer_fix_wildcards (vars, pat, guard, rh) = let
  val var_l = pairSyntax.strip_pair vars
  val (wc_l, var_l') = partition varname_starts_with_uscore var_l

  fun mk_fake wc = mk_var (GrammarSpecials.mk_fakeconst_name {fake = "_", original = NONE}, type_of wc)

  val fake_subst = map (fn wc => (wc |-> mk_fake wc)) wc_l

  val vars' =
    if (List.null var_l') then
      variant (free_varsl [pat, guard, rh]) ``uv:unit``
    else
      pairSyntax.list_mk_pair var_l'

  val pat' = Term.subst fake_subst pat
  val guard' = Term.subst fake_subst guard
  val rh' = Term.subst fake_subst rh
in
  (vars', pat', guard', rh')
end handle HOL_ERR _ => (vars, pat, guard, rh)



fun pmatch_printer GS backend sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open Portable term_pp_types smpp
    infix >>
    val _ = if (!use_pmatch_pp) then () else raise term_pp_types.UserPP_Failed
    val {add_string,add_break,ublock,add_newline,ustyle,...} = ppfns
    val (v,rows) = dest_PMATCH t;
    val rows' = map (fn t => pmatch_printer_fix_wildcards (dest_PMATCH_ROW_ABS t)) rows

    fun pp_row (vars, pat, guard, rh) = (
      term_pp_utils.record_bvars (pairSyntax.strip_pair vars) (
      ublock PP.INCONSISTENT 5 (
        (if ((type_of vars = oneSyntax.one_ty) andalso
            not (free_in vars pat) andalso
            not (free_in vars guard) andalso
            not (free_in vars rh)) then (
          add_string "||." >> add_break (1, 0)
        ) else (
          add_string "||" >>
          add_break (1, 0) >>
          sys (Top, Top, Top) (d - 1) vars >>
          add_string "." >>
          add_break (1, 0)
        )) >>
        sys (Top, Top, Top) (d - 1) pat >>
        (if (aconv guard T) then nothing else (
          add_string " when" >> add_break (1, 0) >>
          sys (Top, Prec (2000, ""), Top) (d - 1) guard
        )) >>
        add_string " ~>" >> add_break (1, 0) >>
        sys (Top, Prec (2000, ""), Top) (d - 1) rh
      ))
    )
  in ublock PP.CONSISTENT 0 (
     (ublock PP.CONSISTENT 2 (add_string "CASE" >> add_break(1,2) >>
       sys (Top, Top, Top) (d - 1) v >>
       add_break(1,0) >> add_string "OF [")) >>
     add_break (1, 2) >>
     ublock PP.CONSISTENT 0 (
       smpp.pr_list pp_row (add_string ";" >> add_break (1, 0)) rows'
     ) >>
     add_break (1, 0) >>
     add_string "]"
  )
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _ = temp_add_user_printer ("PMATCH", ``PMATCH v l``, pmatch_printer);

(***********************************************)
(* Parser                                      *)
(***********************************************)


fun case_magic_to_deep_case t = let
  val rows = strip_conj t

  val v = rator (lhs (hd rows))
  val (arg_tyL, res_ty) = strip_fun (type_of v)

  fun process_row row = let
    val (l,r) = dest_eq row
    val p = rand l

    val vars = free_vars_lr p
  in
    mk_PMATCH_ROW_PABS vars (p, T, r)
  end

  val prows = map process_row rows
  val i = genvar (hd arg_tyL)
  val prows' = listSyntax.mk_list (prows, type_of (hd prows))
  val pmatch_t = mk_PMATCH i prows'
in
  mk_abs (v, mk_abs (i, pmatch_t))
end


val parse_case_as_pmatch = ref false
val _ = Feedback.register_btrace ("parse deep cases", parse_case_as_pmatch);

val _ =
  let fun lookup s =
        case TypeBase.read s
         of SOME tyi => SOME {constructors = TypeBasePure.constructors_of tyi,
                              case_const = TypeBasePure.case_const_of tyi}
          | NONE => NONE
      open GrammarSpecials
  in
    set_case_specials ((fn t =>
      if !parse_case_as_pmatch then
         case_magic_to_deep_case t
      else
         #functional (Pmatch.mk_functional lookup t)),

                       (fn s =>
                             case lookup s of
                               NONE => []
                             | SOME {constructors,...} => constructors))
  end;


val PMATCH_magic_1_tm = mk_const ("PMATCH_magic_1", ``:'a -> ('a -> 'b option) list -> 'b``);
val PMATCH_ROW_magic_0_tm = mk_const ("PMATCH_ROW_magic_0",
  ``:'a # bool # 'b -> 'a -> 'b option``);
val PMATCH_ROW_magic_1_tm = mk_const ("PMATCH_ROW_magic_1",
  ``:('a -> 'b # bool # 'c) -> 'b -> 'c option``);
val PMATCH_ROW_magic_2_tm = mk_const("PMATCH_ROW_magic_2",
  ``:'a -> bool -> 'b -> 'a # bool # 'b``);
val PMATCH_ROW_magic_3_tm = mk_const("PMATCH_ROW_magic_3",
  ``:'a -> 'b -> 'a # bool # 'b``);
val PMATCH_ROW_magic_4_tm = mk_const ("PMATCH_ROW_magic_4",
  ``:'a # bool # 'b -> 'a -> 'b option``);

val _ = temp_add_rule{pp_elements = [TOK "~>"],
                 fixity = Infix (NONASSOC, 3),
                 block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                 paren_style = OnlyIfNecessary,
                 term_name = "PMATCH_ROW_magic_3"}

val _ = temp_add_rule{term_name = "PMATCH_ROW_magic_2",
      fixity = Infix (HOLgrammars.NONASSOC, 3),
      pp_elements = [TOK "when", TM, TOK "~>"],
      paren_style = OnlyIfNecessary,
      block_style = (AroundEachPhrase,
        (PP.INCONSISTENT, 0))};

val _ = temp_add_rule{term_name = "PMATCH_ROW_magic_1",
      fixity = Binder,
      pp_elements = [TOK "||"],
      paren_style = OnlyIfNecessary,
      block_style = (AroundEachPhrase,
        (PP.INCONSISTENT, 0))};

val _ = temp_add_rule{term_name = "PMATCH_ROW_magic_0",
      fixity = Prefix 2,
      pp_elements = [TOK "||."],
      paren_style = OnlyIfNecessary,
      block_style = (AroundEachPhrase,
        (PP.INCONSISTENT, 0))};

val _ = temp_add_rule{term_name = "PMATCH_ROW_magic_4",
      fixity = Prefix 2,
      pp_elements = [TOK "||!"],
      paren_style = OnlyIfNecessary,
      block_style = (AroundEachPhrase,
        (PP.INCONSISTENT, 0))};

val _ = temp_add_rule{term_name = "PMATCH_magic_1",
      fixity = Closefix,
      pp_elements = [TOK "CASE", TM, TOK "OF"],
      paren_style = OnlyIfNecessary,
      block_style = (AroundEachPhrase,
        (PP.INCONSISTENT, 0))};



fun traverse f tm =
  f tm handle HOL_ERR _ =>
  let
    val (tm1, tm2) = dest_comb tm
  in
    mk_comb (traverse f tm1, traverse f tm2)
  end handle HOL_ERR _ =>
  let
    val (tm1, tm2) = dest_abs tm
  in
    mk_abs (traverse f tm1, traverse f tm2)
  end handle HOL_ERR _ => tm;


fun fix_CASE tm = let
     val (c, args) = strip_comb tm
   in
   if (same_const c PMATCH_magic_1_tm) then
     let
       val tys = match_type (type_of PMATCH_magic_1_tm) (type_of c)
       val c' = inst tys PMATCH_tm;
       val args' = map (traverse fix_CASE) args
     in
       list_mk_comb (c', args')
     end
   else if (same_const c PMATCH_ROW_magic_1_tm) orelse (same_const c PMATCH_ROW_magic_0_tm) orelse (same_const c PMATCH_ROW_magic_4_tm) then
     let
       val args' = map (traverse fix_CASE) args
       val (vars, b) =
          if (same_const c PMATCH_ROW_magic_1_tm) then let
            val (p_var, b) = dest_pabs (hd args')
            val vars = pairSyntax.strip_pair p_var
          in
            (vars, b)
          end else if (same_const c PMATCH_ROW_magic_4_tm) then let
            val b = hd args'
            val (_, b_args) = strip_comb b;
            val vars = List.filter (not o varname_starts_with_uscore)
                          (free_vars_lr (el 1 b_args))
          in
            (vars, b)
          end else (* magic 0 *) ([], hd args');
       val (b_c, b_args) = strip_comb b;
       val (p, g, r) = if (same_const b_c PMATCH_ROW_magic_2_tm) then
            (el 1 b_args, el 2 b_args, el 3 b_args)
          else if (same_const b_c PMATCH_ROW_magic_3_tm) then
            (el 1 b_args, T, el 2 b_args)
          else failwith "unexpected constant";
       val wildcards = List.filter varname_starts_with_uscore (
          free_vars p
       )
       val vars = vars @ wildcards
     in
       mk_PMATCH_ROW_PABS vars (p, g, r)
     end
   else failwith "no CASE"
end;

(*
Preterm.post_process_term := I *)
val old_f = !Preterm.post_process_term;
val _ = (Preterm.post_process_term := (fn tm => (traverse fix_CASE (old_f tm))));




end


