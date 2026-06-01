structure Typetab = Table(
  type key = Type.hol_type
  val ord = Type.compare
  fun simple_print ty =
      let open HOLPP Type
      in
        if is_vartype ty then add_string (dest_vartype ty)
        else
          let val {Thy, Tyop, Args} = dest_thy_type ty
              val opname = Thy ^ "$" ^ Tyop
          in
            case Args of
                [] => add_string opname
              | _ =>
                block CONSISTENT 0 [
                  add_string "(",
                  block INCONSISTENT 1 (
                    pr_list simple_print [add_break(1,0)] Args
                  ),
                  add_string (")" ^ opname)
                ]
          end
      end
  val pp = simple_print
)
