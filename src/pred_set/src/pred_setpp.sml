structure pred_setpp :> pred_setpp =
struct

open HolKernel

val univ_printing = ref true
val unicode_univ = ref true

val _ = Feedback.register_btrace ("Univ pretty-printing", univ_printing)
val _ = Feedback.register_btrace ("Unicode Univ printing", unicode_univ)
          (* because the current unicode symbol for the universal set is
             beyond the BMP, it may not be common in installed fonts.
             So we provide a flag specifically to turn just it off. *)

fun univ_printer (tyg, tmg) backend printer ppfns gravs depth tm =
  let
    open smpp infix >>
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

end
