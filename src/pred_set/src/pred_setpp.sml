structure pred_setpp :> pred_setpp =
struct

open HolKernel smpp term_pp_types term_pp_utils

val univ_printing = ref true
val unicode_univ = ref true

val _ = Feedback.register_btrace ("Univ pretty-printing", univ_printing)
val _ = Feedback.register_btrace ("Unicode Univ printing", unicode_univ)
          (* because the current unicode symbol for the universal set is
             beyond the BMP, it may not be common in installed fonts.
             So we provide a flag specifically to turn just it off. *)

fun univ_printer (tyg, tmg) backend printer ppfns gravs depth tm =
  let
    val {add_string, ...} = ppfns : term_pp_types.ppstream_funs
  in
    if !univ_printing then
      let
        val (elty, _) = dom_rng (type_of tm)
        val itself_t = Term.inst [{redex=alpha,residue=elty}]
                                 boolSyntax.the_value
        val U = if get_tracefn "Unicode" () = 1 andalso !unicode_univ then
                  UnicodeChars.universal_set
                else "univ"
      in
        add_string U >>
        printer {gravs = gravs, depth = depth, binderp = false} itself_t
      end
    else
      case Overload.info_for_name (term_grammar.overload_info tmg) "UNIV" of
          NONE => add_string "pred_set$UNIV"
        | SOME _ => add_string "UNIV"
  end

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "pred_set.UNIV", code = univ_printer}

(* ----------------------------------------------------------------------
    A flag controlling printing of set comprehensions
   ---------------------------------------------------------------------- *)

val unamb_comp = ref 0
val _ = Feedback.register_trace ("pp_unambiguous_comprehensions", unamb_comp, 2)


fun setcomprehension_printer (tyg,tmg) backend printer ppfns gravs depth tm =
    let
      val unamb_comp = get_tracefn "pp_unambiguous_comprehensions" ()
      val _ =
          case Overload.oi_strip_comb (term_grammar.overload_info tmg) tm of
              SOME(f, _) =>
                if term_grammar.grammar_name tmg f = SOME "GSPEC"
                then ()
                else raise UserPP_Failed
            | NONE => raise UserPP_Failed
      val _ = term_pp_utils.pp_is_abs tmg (rand tm) orelse raise UserPP_Failed
      val {add_string, add_break, ...} = ppfns : term_pp_types.ppstream_funs
      fun hardspace n = add_string (CharVector.tabulate(n, fn _ => #" "))
      fun spacep b = if b then add_break(1,0) else nothing

      val (vs, body) = term_pp_utils.pp_dest_abs tmg (rand tm)
      val vfrees = FVL [vs] empty_tmset
      val bvars_seen_here = HOLset.listItems vfrees

      val (l, r) = pairSyntax.dest_pair body
      val lfrees = FVL [l] empty_tmset
      val rfrees = FVL [r] empty_tmset
      open HOLset
      val tops = (Top,Top,Top)
      fun pr t =
          printer {gravs = tops, depth = decdepth depth, binderp = false} t
    in
      if ((equal(intersection(lfrees,rfrees), vfrees) orelse
           (isEmpty lfrees andalso equal(rfrees, vfrees)) orelse
           (isEmpty rfrees andalso equal(lfrees, vfrees)))
          andalso unamb_comp = 0) orelse
         unamb_comp = 2
      then
        block PP.CONSISTENT 0 (
          record_bvars bvars_seen_here (
            set_gspec (
              add_string "{" >>
              block PP.CONSISTENT 1 (
                pr l >> hardspace 1 >> add_string "|" >> spacep true >> pr r
              ) >>
              add_string "}"
            )
          )
        )
      else
        block PP.CONSISTENT 0 (
          record_bvars bvars_seen_here (
            set_gspec (
              add_string "{" >>
              block PP.CONSISTENT 1 (
                pr l >> hardspace 1 >> add_string "|" >> spacep true >> pr vs >>
                hardspace 1 >> add_string "|" >> spacep true >>
                pr r
              ) >>
              add_string "}"
            )
          )
        )
    end handle HOL_ERR _ => raise UserPP_Failed

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "pred_set.GSPEC", code = setcomprehension_printer}


end
