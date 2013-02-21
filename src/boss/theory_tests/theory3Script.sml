(* a TFL bug *)

open HolKernel Parse boolLib bossLib

open optionTheory
open monadsyntax

val _ = new_theory "theory3";
val _ = overload_on ("monad_bind", ``OPTION_BIND``)

val _ = Hol_datatype `nt = NT1 | NT2`;

val _ = new_type ("ast", 0)

val _ = Hol_datatype`gtok = NT of nt | TOK of num`

val _ = Hol_datatype`ptree = Lf of gtok | Nd of nt => ptree list`

val _ = new_constant("Ast_Tapp", ``:ast list -> num -> ast``);

val works_ptree_Type_def = Define`
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
`


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



val _ = export_theory()
