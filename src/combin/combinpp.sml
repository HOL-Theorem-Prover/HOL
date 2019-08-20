structure combinpp :> combinpp =
struct

open HolKernel boolLib Absyn
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
           | SOME (_, arg10, arg20) =>
             let
               val arg1 = upd_processor G arg10
               val arg2 = upd_processor G arg20
             in
               process_updates arg1 arg2
             end)
      | _ => a;

val _ = term_grammar.userSyntaxFns.register_absynPostProcessor
          {name = "combin.UPDATE", code = upd_processor}

fun has_name_by_parser G s tm = let
  open GrammarSpecials
  val oinfo = term_grammar.overload_info G
in
  case dest_term tm of
      VAR(vnm, _) => vnm = s orelse
                     (case dest_fakeconst_name vnm of
                          SOME{fake,...} => fake = s
                        | NONE => false)
    | _ =>
      (case Overload.info_for_name oinfo s of
           NONE => false
         | SOME {actual_ops,...} =>
             List.exists (fn t => can (match_term t) tm) actual_ops)
end
fun isupdate_tm G t = has_name_by_parser G "UPDATE" t

fun strip_upd G t =
    let
      fun recurse A t =
          case strip_comb t of
              (u, [k,v,f]) => if isupdate_tm G u then
                                recurse ((k,v)::A) f
                              else (List.rev A, t)
            | _ => (List.rev A, t)
    in
      recurse [] t
    end

fun upd_printer (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
    let
      open term_pp_utils term_pp_types smpp
      val unicodep = get_tracefn "PP.avoid_unicode" () = 0
      val (kvs, f) = strip_upd tmg tm
      val _ = not (null kvs) orelse raise UserPP_Failed
      val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs
      val (arrow_s,ld_s,rd_s) = if unicodep then ("↦", "⦇", "⦈") (* UOK *)
                                else ("|->", "(|", "|)")
      val paren =
          case lgr of
              Prec(i, _) => if i > 2100 then
                              fn p => block PP.INCONSISTENT 1 (
                                       add_string "(" >> p >>
                                       add_string ")"
                                     )
                            else (fn p => p)
            | _ => fn p => p
      val arrow_grav = Prec(100, mapsto_special)
      val mygrav = case Parse.fixity ld_s of
                       SOME (term_grammar.Suffix i) => Prec(i, ld_s)
                     | _ => raise UserPP_Failed
      fun prkv (k,v) =
          block PP.INCONSISTENT 2 (
            printer {gravs = (arrow_grav,Top,arrow_grav),
                     depth = decdepth depth, binderp = false} k >>
            add_string " " >> add_string arrow_s >> add_break(1,0) >>
            printer {gravs = (arrow_grav,Top,arrow_grav),
                     depth = decdepth depth, binderp = false} v
          )
    in
      paren (
        block PP.CONSISTENT 0 (
          printer {gravs = (pgr,lgr,mygrav), depth = decdepth depth,
                   binderp = false} f >>
          add_string ld_s >> add_break(0,2) >>
          block PP.INCONSISTENT 0 (
            pr_list prkv (add_string ";" >> add_break(1,0)) kvs
          ) >> add_break (0,0) >>
          add_string rd_s
        )
      )
    end

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "combin.updpp", code = upd_printer}

end (* struct *)
