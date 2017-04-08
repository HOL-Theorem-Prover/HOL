structure boolpp :> boolpp =
struct

open Parse HolKernel

fun dest_cond tm =
  let
    val (f, args) = strip_comb tm
    val {Thy,Name,...} = dest_thy_const f
      handle HOL_ERR _ =>
             raise mk_HOL_ERR "boolpp" "dest_cond" "Not even a const at head"
  in
    if Thy = "bool" andalso Name = "COND" then
      case args of
          [gd, th, el] => (gd,th,el)
        | _ => raise mk_HOL_ERR "boolpp" "dest_cond" "Wrong number of arguments"
    else
      raise mk_HOL_ERR "boolpp" "dest_cond" "Not a COND-term"
  end

fun condprinter (tyg, tmg) backend printer ppfns (pgr,lgr,rgr) depth tm = let
  open term_pp_types smpp
  infix >>
  val _ =
      case Overload.oi_strip_comb (term_grammar.overload_info tmg) tm of
          SOME(f, _) =>
            if term_grammar.grammar_name tmg f = SOME "case"
            then ()
            else raise UserPP_Failed
        | NONE => raise UserPP_Failed
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
  fun syspr gravs t =
    printer { gravs = gravs, depth = depth - 1, binderp = false } t
  fun doguard needs_else (g,t) =
      block PP.CONSISTENT 0
            (block PP.CONSISTENT 0
                   ((if needs_else then
                       add_string "else" >> add_string " " >>
                       add_string "if"
                     else
                       add_string "if") >>
                    add_break (1,2) >>
                    syspr (Top,Top,Top) g >>
                    add_break (1,0) >>
                    add_string "then") >>
             add_break (1,2) >>
             syspr (Top,Top,Top) t)

  fun doelse e = let
    val prec = Prec(70, "COND")
  in
    case Lib.total dest_cond e of
        SOME (g,t,e_next) => (doguard true (g,t) >> add_break(1,0) >>
                              doelse e_next)
      | NONE => block PP.CONSISTENT 0
                      (add_string "else" >> add_break (1,2) >>
                       syspr (prec,prec,rgr) e)
  end
  val (g,t,e) = dest_cond tm
in
  doparen "(" >>
  block PP.CONSISTENT 0
    (doguard false (g,t) >> add_break(1,0) >> doelse e) >>
  doparen ")"
end

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "bool.COND", code = condprinter}

end
