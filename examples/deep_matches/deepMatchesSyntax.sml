structure deepMatchesSyntax :> deepMatchesSyntax =
struct

open deepMatchesTheory bossLib 


(***********************************************)
(* Terms                                       *)
(***********************************************)

val PMATCH_ROW_tm = ``PMATCH_ROW``
val PMATCH_tm = ``PMATCH``

(***********************************************)
(* Matching support                            *)
(***********************************************)

val thm = PMATCH_REMOVE_ARB_NO_OVERLAP

fun FRESH_TY_VARS_RULE thm = let
  val (vars0, _) = strip_forall (concl thm)
  val vars1 = free_vars (concl thm) 
  val vars = vars0 @ vars1
  val tys = type_varsl (map type_of vars) 
  val subst = map (fn ty => (ty |-> gen_tyvar ())) tys 
in
  INST_TYPE subst thm
end 

(***********************************************)
(* PMATCH_ROW                                  *)
(***********************************************)

fun dest_PMATCH_ROW row = let
  val (f, args) = strip_comb row
  val _ = if (same_const f PMATCH_ROW_tm) andalso (List.length args = 1) then () else failwith "dest_PMATCH_ROW"

  val arg = hd args

  val (vars_tm, prh) = pairSyntax.dest_pabs arg
  val (p, rh) = pairSyntax.dest_pair prh
in
  (vars_tm, p, rh)
end

fun is_PMATCH_ROW t = can dest_PMATCH_ROW t

fun mk_PMATCH_ROW vars p rh = let
  val prh = pairSyntax.mk_pair(p, rh) 
  val pabs = case vars of
      []  => mk_abs (genvar ``:unit``, prh)
    | [v] => mk_abs (v, prh)
    | _   => pairSyntax.mk_pabs (pairSyntax.list_mk_pair vars, prh)
  in
    mk_icomb (PMATCH_ROW_tm, pabs)
  end


fun PMATCH_ROW_PABS_ELIM_CONV r = let
  val (vars, _, _) = dest_PMATCH_ROW r
  val thm = (RAND_CONV pairTools.PABS_ELIM_CONV) r
in
  (vars, thm)
end

fun PMATCH_ROW_PABS_INTRO_CONV vars r = let
  val _ = if (is_PMATCH_ROW r) then () else failwith "PMATCH_ROW_PABS_INTRO_CONV"
  val thm = (RAND_CONV (pairTools.PABS_INTRO_CONV vars)) r
in
  thm
end



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
    val (vars_tm, pt, rh) = dest_PMATCH_ROW r
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

    val rows' = map dest_PMATCH_ROW rows

    fun pp_row (vars, pat, rh) = (   
      term_pp_utils.record_bvars (pairSyntax.strip_pair vars) (
      ublock PP.CONSISTENT 0 (
        add_string "|" >> add_break (1, 0) >>
        sys (Top, Top, Top) (d - 1) pat >>
        add_break (1, 0) >> add_string "=>" >> add_break (1, 0) >>
        sys (Top, Top, Top) (d - 1) rh 
      ))
    )
  in
     (ublock PP.CONSISTENT 2 (add_string "CASE" >> add_break(1,2) >>
       sys (Top, Top, Top) (d - 1) v >>
       add_break(1,0) >> add_string "OF")) >>
     add_break (1, 0) >>
     smpp.pr_list pp_row (add_break (0, 0)) rows'
  end handle HOL_ERR _ => raise term_pp_types.UserPP_Failed;

val _ = add_user_printer ("PMATCH", ``PMATCH v l``, pmatch_printer);

end
