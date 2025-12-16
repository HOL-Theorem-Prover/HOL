(* a TFL bug *)
Theory theory3
Ancestors
  option
Libs
  monadsyntax


val _ = temp_add_monadsyntax()
Overload monad_bind = ``OPTION_BIND``

Datatype: nt = NT1 | NT2
End

val _ = new_type ("ast", 0)

Datatype: gtok = NT nt | TOK num
End

Datatype: ptree = Lf gtok | Nd nt (ptree list)
End

val _ = new_constant("Ast_Tapp", ``:ast list -> num -> ast``);

Definition works_ptree_Type_def:
  works_ptree_Type ptree =
    case ptree of
      Nd nt args =>
      (case nt of
         NT1 => (case args of
                   [Lf _] => NONE
                 | [dt; opn] => do
                     dty <- works_ptree_Type dt;
                     SOME (Ast_Tapp [dty] 201)
                   od
                 | _ => NONE)
       | _ => NONE)
    | _ => NONE
End


val fails_ptree_Type_def = Pmatch.with_classic_heuristic Define `
  fails_ptree_Type ptree =
    case ptree of
      Lf _ => NONE
    | Nd nt args =>
      (case nt of
         NT1 => (case args of
                   [Lf _] => NONE
                   (* comment out line above, and it works OK *)
                 | [dt; opn] => do
                     dty <- fails_ptree_Type dt;
                     SOME (Ast_Tapp [dty] 201)
                   od
                 | _ => NONE)
       | _ => NONE)
`
