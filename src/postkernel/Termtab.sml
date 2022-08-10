structure Termtab = Table(
  type key = Term.term
  val ord = Term.compare
  fun strip_comb0 A t =
      case Term.dest_term t of
          Term.COMB (f, x) => strip_comb0 (x::A) f
        | _ => (t, A)
  fun strip_comb t = strip_comb0 [] t
  fun strip_abs0 A t =
      case Term.dest_term t of
          Term.LAMB(v,body) => strip_abs0 (v::A) body
        | _ => (List.rev A, t)
  fun strip_abs t = strip_abs0 [] t
  fun simple_print t =
      let
        open HOLPP Term
      in
        case dest_term t of
            CONST {Name,Thy,...} => add_string (Thy  ^ "$" ^ Name)
          | VAR (s,_) => add_string s
          | COMB _ =>
            let
              val (f, xs) = strip_comb t
            in
              block CONSISTENT 0 [
                add_string "(",
                block INCONSISTENT 1 (
                  pr_list simple_print [add_break(1,0)] (f::xs)
                ),
                add_string ")"
              ]
            end
          | LAMB _ =>
            let
              val (vs, body) = strip_abs t
            in
              block CONSISTENT 0 [
                add_string "(\\ (",
                block INCONSISTENT 4 (
                  pr_list simple_print [add_break (1,0)] vs
                ),
                add_string ")",
                add_break(1,2),
                simple_print body,
                add_string ")"
              ]
            end
      end
  val pp = simple_print
)
