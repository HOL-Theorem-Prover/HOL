structure combinpp :> combinpp =
struct

open Absyn
val toplevel_updname = "  combinpp.toplevelupd"
val internal_consupd = "  combinpp.cons"
val internal_idupd = "  combinpp.nil"
val mapsto_special = "  combinpp.leftarrow"
val update_constname = "combinpp.UPDATE"

fun ERR f l msg = Feedback.mk_HOL_ERRloc "combinpp" f l msg
fun cAPP l (a1, a2) = Absyn.APP(l,a1,a2)

fun break_binop ident a =
    case a of
        APP(l, a1, a2) =>
          (case a1 of
               APP(l1, IDENT (l1', s), a12) =>
               if s = ident then SOME (l, a12, a2)
               else NONE
             | _ => NONE)
      | _ => NONE

fun break_arrow a =
    case break_binop mapsto_special a of
        SOME(l, a1, a2) => (a1,a2)
      | NONE => raise ERR "upd_processor" (locn_of_absyn a)
                      "Expected to find maps-to form"

fun process_updates f upds =
    case upds of
        IDENT (l, inner) => if inner = internal_idupd then f
                            else raise ERR "upd_processor" l
                                       "Fn-update syntax bottoms out badly"
      | _ =>
          (case break_binop internal_consupd upds of
               SOME (l, arg1, arg2) =>
               let
                 val (d,r) = break_arrow arg1
                 val t = process_updates f arg2
               in
                 cAPP l (
                   cAPP (locn.between (locn_of_absyn d) (locn_of_absyn r)) (
                     cAPP (locn_of_absyn d) (
                       IDENT (locn.Loc_None, update_constname),
                       d
                     ),
                     r
                   ),
                   t
                 )
               end
             | NONE => raise ERR "upd_processor" (locn_of_absyn upds)
                             "Fn-update syntax update broken")

fun upd_processor G a =
    case a of
        LAM (l,v,a0) => LAM (l,v,upd_processor G a0)
      | TYPED (l, a0, pty) => TYPED(l, upd_processor G a0, pty)
      | APP(l,a1,a2) =>
        (case break_binop toplevel_updname a of
             NONE => APP(l, upd_processor G a1, upd_processor G a2)
           | SOME (_, arg1, arg2) => process_updates arg1 arg2)
      | _ => a;

val _ = term_grammar.userSyntaxFns.register_absynPostProcessor
          {name = "combin.UPDATE", code = upd_processor}






end (* struct *)
