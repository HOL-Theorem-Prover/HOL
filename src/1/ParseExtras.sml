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
  fun doguard needs_else (g,t) =
      block PP.CONSISTENT 0
            (block PP.CONSISTENT 0
                   ((if needs_else then
                       add_string "else" >> add_string " " >>
                       add_string "if"
                     else
                       add_string "if") >>
                    add_break (1,2) >>
                    printer (Top,Top,Top) (depth - 1) g >>
                    add_break (1,0) >>
                    add_string "then") >>
             add_break (1,2) >>
             printer (Top,Top,Top) (depth - 1) t)

  fun doelse e = let
    val prec = Prec(70, "COND")
  in
    case Lib.total dest_cond e of
        SOME (g,t,e_next) => (doguard true (g,t) >> add_break(1,0) >>
                              doelse e_next)
      | NONE => block PP.CONSISTENT 0
                      (add_string "else" >> add_break (1,2) >>
                       printer (prec,prec,rgr) (depth - 1) e)
  end
  val (g,t,e) = dest_cond tm
in
  doparen "(" >>
  block PP.CONSISTENT 0
    (doguard false (g,t) >> add_break(1,0) >> doelse e) >>
  doparen ")"
end

val cond_t = mk_cond (mk_var("p", bool), mk_var("q", alpha), mk_var("r", alpha))
val _ = temp_add_user_printer ("COND", cond_t, condprinter)

end
