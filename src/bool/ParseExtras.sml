structure ParseExtras :> ParseExtras =
struct

open Parse HolKernel boolSyntax

fun tight_equality() = set_fixity "=" (Infix(NONASSOC, 450))

fun condprinter (tyg, tmg) printer ppfns (pgr,lgr,rgr) depth pps tm = let
  open term_pp_types
  val {add_string, begin_block, end_block, add_break, ...} = ppfns:ppstream_funs
  val paren_required =
      (case rgr of
         Prec(p, _) => p > 70
       | _ => false) orelse
      (case lgr of
         Prec(_, n) => n = GrammarSpecials.fnapp_special
       | _ => false)
  val doparen = if paren_required then (fn c => add_string c) else (fn c => ())
  fun doone (guard, t, e) = let
  in
    (* A begin_block done by caller *)
    (* begin_block PP.CONSISTENT  0; *)
      add_string "if";
      add_break (1,2);
      printer (Top,Top,Top) (depth - 1) guard;
      add_break (1,0);
      add_string "then";
    end_block();
    add_break(1,2);
    printer (Top,Top,Top) (depth -1) t;
    add_break(1,0);
    if is_cond e then
      (begin_block PP.CONSISTENT 0;
       add_string "else"; add_string " ";
       doone(dest_cond e))
    else
      (add_string "else";
       add_break (1,2);
       printer (Prec(70, "COND"), Prec(70, "COND"), rgr) (depth - 1) e)
  end
in
  doparen "(";
  begin_block PP.CONSISTENT 0;
  begin_block PP.CONSISTENT 0;
  doone (dest_cond tm);
  end_block();
  doparen ")"
end

val cond_t = mk_cond (mk_var("p", bool), mk_var("q", alpha), mk_var("r", alpha))
val _ = temp_add_user_printer ("COND", cond_t, condprinter)

end
