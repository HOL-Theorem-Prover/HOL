structure monadsyntax :> monadsyntax =
struct

open HolKernel Parse Feedback

local open state_transformerTheory in end

val monadseq_special = "__monad_sequence"
val monad_emptyseq_special = "__monad_emptyseq"
val monadassign_special = "__monad_assign"
val monad_unitbind = "monad_unitbind"
val monad_bind = "monad_bind"

val _ = temp_add_listform {block_info = (PP.CONSISTENT,0),
                           cons = monadseq_special,
                           nilstr = monad_emptyseq_special,
                           leftdelim = [TOK "do", BreakSpace(1,2)],
                           rightdelim = [TOK "od"],
                           separator = [TOK ";", BreakSpace(1,0)]}

val _ = temp_add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                       fixity = Infix(NONASSOC, 100),
                       paren_style = OnlyIfNecessary,
                       pp_elements = [BreakSpace(1,0), TOK "<-", HardSpace 1],
                       term_name = monadassign_special}

fun to_vstruct a = let
  open Absyn
in
  case a of
    AQ x => VAQ x
  | IDENT x => VIDENT x
  | QIDENT(loc,_,_) =>
    raise mk_HOL_ERRloc "Absyn" "to_vstruct" loc
                        "Qualified identifiers can't be varstructs"
  | APP(loc1, APP(loc2, IDENT (loc3, ","), arg1), arg2) =>
      VPAIR(loc1, to_vstruct arg1, to_vstruct arg2)
  | TYPED (loc, a0, pty) => VTYPED(loc, to_vstruct a0, pty)
  | _ => raise mk_HOL_ERRloc "Absyn" "to_vstruct" (locn_of_absyn a)
                             "Bad form of varstruct"
end

fun clean_action a = let
  open Absyn
in
  case a of
    APP(loc1, APP(loc2, IDENT(loc3, s), arg1), arg2) => let
    in
      if s = monadassign_special then
        (SOME (to_vstruct arg1), arg2)
      else (NONE, a)
    end
  | _ => (NONE, a)
end

fun cleanseq a = let
  open Absyn
in
  case a of
    APP(loc1, APP(loc2, IDENT(loc3, s), arg1), arg2) => let
    in
      if s = monadseq_special then let
          val (bv, arg1') = clean_action (clean_do true arg1)
          val arg2' = clean_actions arg2
        in
          case arg2' of
            NONE => SOME arg1'
          | SOME a => let
            in
              case bv of
                NONE => SOME (APP(loc1,
                                  APP(loc2,
                                      IDENT(loc3, monad_unitbind),
                                      arg1'),
                                  a))
              | SOME b => SOME (APP(loc1,
                                    APP(loc2,
                                        IDENT(loc3, monad_bind),
                                        arg1'),
                                    LAM(locn_of_absyn a, b, a)))
            end
        end
      else NONE
    end
  | _ => NONE
end
and clean_do indo a = let
  open Absyn
  val clean_do = clean_do indo
in
  case cleanseq a of
    SOME a => a
  | NONE => let
    in
      case a of
        APP(l,arg1 as APP(_,IDENT(_,s),_),arg2) =>
        if s = monadassign_special andalso not indo then
          raise mk_HOL_ERRloc "monadsyntax" "clean_do" l
                              "Bare monad assign arrow illegal"
        else APP(l,clean_do arg1,clean_do arg2)
      | APP(l,a1,a2) => APP(l,clean_do a1, clean_do a2)
      | LAM(l,v,a) => LAM(l,v,clean_do a)
      | IDENT(loc,s) => if s = monad_emptyseq_special then
                          raise mk_HOL_ERRloc "monadsyntax" "clean_do" loc
                                              "Empty do-od pair illegal"
                        else a
      | TYPED(l,a,pty) => TYPED(l,clean_do a, pty)
      | _ => a
    end
end
and clean_actions a = let
  open Absyn
in
  case cleanseq a of
    SOME a => SOME a
  | NONE => let
    in
      case a of
        IDENT(loc,s) => if s = monad_emptyseq_special then NONE
                        else SOME a
      | a => SOME a
    end
end

val transform_absyn = clean_do false

val _ = Parse.temp_add_absyn_postprocessor ("monadsyntax.transform_absyn",
                                            transform_absyn)


fun dest_bind G t = let
  open term_pp_types
  val oinfo = term_grammar.overload_info G
  val (fx, y) = dest_comb t
  val (f, x) = dest_comb fx
  val prname = case Overload.overloading_of_term oinfo f of
                 NONE => if is_var f then #1 (dest_var f)
                         else raise UserPP_Failed
               | SOME s => s
  val _ = prname = monad_unitbind orelse
          (prname = monad_bind andalso pairSyntax.is_pabs y) orelse
          raise UserPP_Failed
in
  SOME (prname, x, y)
end handle HOL_ERR _ => NONE
         | term_pp_types.UserPP_Failed =>  NONE


fun print_monads (tyg, tmg) backend sysprinter ppfns (p,l,r) dpth t = let
  open term_pp_types term_grammar smpp term_pp_utils
  infix >>
  val ppfns = ppfns :ppstream_funs
  val {add_string=strn,add_break=brk,ublock,...} = ppfns
  val (prname, arg1, arg2) = valOf (dest_bind tmg t)
                             handle Option => raise UserPP_Failed
  fun pr_action (v, action) =
      case v of
        NONE => sysprinter (Top,Top,Top) (dpth - 1) action
      | SOME v => let
          val bvars = free_vars v
        in
          addbvs bvars >>
          ublock PP.INCONSISTENT 0
            (sysprinter (Top,Top,Prec(100, "monad_assign")) (dpth - 1) v >>
             strn " " >> strn "<-" >> brk(1,2) >>
             sysprinter (Top,Prec(100, "monad_assign"),Top) (dpth - 1) action)
        end
  fun brk_bind binder arg1 arg2 =
      if binder = monad_bind then let
              val (v,body) = (SOME ## I) (pairSyntax.dest_pabs arg2)
                             handle HOL_ERR _ => (NONE, arg2)
        in
          ((v, arg1), body)
        end
      else ((NONE, arg1), arg2)
  fun strip acc t =
      case dest_bind tmg t of
        NONE => List.rev ((NONE, t) :: acc)
      | SOME (prname, arg1, arg2) => let
          val (arg1', arg2') = brk_bind prname arg1 arg2
        in
          strip (arg1'::acc) arg2'
        end
  val (arg1',arg2') = brk_bind prname arg1 arg2
  val actions = strip [arg1'] arg2'
in
  ublock PP.CONSISTENT 0
    (strn "do" >> brk(1,2) >>
     getbvs >- (fn oldbvs =>
     pr_list pr_action (strn ";" >> brk(1,2)) actions >>
     brk(1,0) >>
     strn "od" >> setbvs oldbvs))
end

val _ = temp_add_user_printer ("monadsyntax.print_monads", ``x:'a``,
                               print_monads)

fun mkc s = prim_mk_const{Thy = "state_transformer", Name = s}
val _ = temp_overload_on (monad_bind, mkc "BIND")
val _ = temp_overload_on (monad_unitbind, mkc "IGNORE_BIND")
val _ = temp_overload_on ("return", mkc "UNIT")

val _ = TexTokenMap.temp_TeX_notation
            {hol = "<-", TeX = ("\\HOLTokenLeftmap", 1)}

end (* struct *)
