structure ParseExtras :> ParseExtras =
struct

open Parse HolKernel boolSyntax

fun tight_equality() = set_fixity "=" (Infix(NONASSOC, 450))

fun condprinter (tyg, tmg) backend printer ppfns (pgr,lgr,rgr) depth tm = let
  open term_pp_types smpp
  infix >>
  val {add_string, ublock, add_break, ...} = ppfns:ppstream_funs
  val paren_required =
      (case rgr of
         Prec(p, _) => p > 70
       | _ => false) orelse
      (case lgr of
         Prec(_, n) => n = GrammarSpecials.fnapp_special
       | _ => false)
  val doparen = if paren_required then (fn c => add_string c)
                else (fn c => nothing)
  fun doguard g =
      add_string "if" >>
      add_break (1,2) >>
      printer (Top,Top,Top) (depth - 1) g >>
      add_break (1,0) >>
      add_string "then"

  fun doone (t, e) = let
  in
    add_break(1,2) >>
    printer (Top,Top,Top) (depth -1) t >>
    add_break(1,0) >>
    (if is_cond e then let
         val (g,t,e) = dest_cond e
       in
         block PP.CONSISTENT 0
               (add_string "else" >> add_string " " >> doguard g) >>
         doone(t,e)
       end
    else
      add_string "else" >>
      add_break (1,2) >>
      printer (Prec(70, "COND"), Prec(70, "COND"), rgr) (depth - 1) e)
  end
  val (g,t,e) = dest_cond tm
in
  doparen "(" >>
  block PP.CONSISTENT 0
    (block PP.CONSISTENT 0 (doguard g) >>
     doone (t, e)) >>
  doparen ")"
end

val cond_t = mk_cond (mk_var("p", bool), mk_var("q", alpha), mk_var("r", alpha))
val _ = temp_add_user_printer ("COND", cond_t, condprinter)

end
