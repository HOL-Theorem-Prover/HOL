structure deepMatchesSyntax :> deepMatchesSyntax =
struct

open deepMatchesTheory bossLib



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
val PMATCH_ROW_gtm = inst ty_var_subst PMATCH_ROW_tm

val PMATCH_tm = ``PMATCH``
val PMATCH_gtm = inst ty_var_subst PMATCH_tm

fun FRESH_TY_VARS_RULE thm =
  INST_TYPE ty_var_subst thm


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

fun mk_PMATCH_ROW_PABS vars (p_t, g_t, r_t) = let
  val mk_pabs = case vars of
      []  => let
               val uv = variant (free_varsl [p_t, g_t, r_t]) ``uv:unit``
             in
               fn t => mk_abs (uv, t)
             end
    | [v] => (fn t => mk_abs (v, t))
    | _   => (fn t => pairSyntax.mk_pabs (pairSyntax.list_mk_pair vars, t))
  in
    mk_PMATCH_ROW (mk_pabs p_t, mk_pabs g_t, mk_pabs r_t)
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
end


fun PMATCH_ROW_PABS_ELIM_CONV row = let
  val (p, _, _) = dest_PMATCH_ROW row
  val (vars, _) = pairSyntax.dest_pabs p

  val c = TRY_CONV pairTools.PABS_ELIM_CONV
  val thm = ((RAND_CONV c) THENC
             (RATOR_CONV (RAND_CONV c)) THENC
             (RATOR_CONV (RATOR_CONV (RAND_CONV c)))) row
            handle UNCHANGED => REFL row
in
  (vars, thm)
end


fun PMATCH_ROW_PABS_INTRO_CONV vars row = let
  val _ = if (is_PMATCH_ROW row) then () else failwith "PMATCH_ROW_PABS_INTRO_CONV"

  val (vars', _) = variant_of_term (free_vars row) vars
  val c = pairTools.PABS_INTRO_CONV vars'
  val thm = ((RAND_CONV c) THENC
             (RATOR_CONV (RAND_CONV c)) THENC
             (RATOR_CONV (RATOR_CONV (RAND_CONV c)))) row
in
  thm
end

fun PMATCH_ROW_FORCE_SAME_VARS_CONV row = let
  val _ = if not (is_PMATCH_ROW row) then raise UNCHANGED else ()
  val _ = if can dest_PMATCH_ROW_ABS row then raise UNCHANGED else ()

  val (vars, thm0) = PMATCH_ROW_PABS_ELIM_CONV row
  val thm1 = PMATCH_ROW_PABS_INTRO_CONV vars (rhs (concl thm0))
in
  TRANS thm0 thm1
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

fun dest_PMATCH_COLS t = let
  val (v, rows) = dest_PMATCH t
  val vs = pairSyntax.strip_pair v

  fun split_row r = let
    val (vars_tm, pt, gt, rh) = dest_PMATCH_ROW_ABS r
    val vars = pairSyntax.strip_pair vars_tm
    val pts = pairSyntax.strip_pair pt
  in
    List.map (fn x => (vars, x)) pts
  end
  val rows' = map split_row rows

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
end handle Empty => failwith "dest_PMATCH_COLS"

fun PMATCH_FORCE_SAME_VARS_CONV t = let
  val _ = if not (is_PMATCH t) then raise UNCHANGED else ()
in
  DEPTH_CONV PMATCH_ROW_FORCE_SAME_VARS_CONV t
end

(***********************************************)
(* Pretty Printing                             *)
(***********************************************)

val use_pmatch_pp = ref true
val _ = Feedback.register_btrace ("use pmatch_pp", use_pmatch_pp);

fun pmatch_printer GS backend sys (ppfns:term_pp_types.ppstream_funs) gravs d t =
  let
    open Portable term_pp_types smpp
    infix >>
    val _ = if (!use_pmatch_pp) then () else raise term_pp_types.UserPP_Failed
    val {add_string,add_break,ublock,add_newline,ustyle,...} = ppfns
    val (v,rows) = dest_PMATCH t;

    val rows' = map dest_PMATCH_ROW_ABS rows

    fun pp_row (vars, pat, guard, rh) = (
      term_pp_utils.record_bvars (pairSyntax.strip_pair vars) (
      ublock PP.CONSISTENT 0 (
        add_string "|" >> add_break (1, 0) >>
        sys (Top, Top, Top) (d - 1) pat >>
        (if (aconv guard T) then nothing else (
          add_break (1, 0) >> add_string "when" >> add_break (1, 0) >>
          sys (Top, Top, Top) (d - 1) guard
        )) >>
        add_break (1, 0) >> add_string "=>" >> add_break (1, 0) >>
        sys (Top, Top, Top) (d - 1) rh
      ))
    )
  in
     (ublock PP.CONSISTENT 2 (add_string "CASE" >> add_break(1,2) >>
       sys (Top, Top, Top) (d - 1) v >>
       add_break(1,0) >> add_string "OF")) >>
     add_break (1, 0) >>
     smpp.pr_list pp_row (add_break (1, 0)) rows'
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _ = add_user_printer ("PMATCH", ``PMATCH v l``, pmatch_printer);


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
  end

end
