
open HolKernel Parse Feedback

local open state_transformerTheory oneTheory in end

val monadseq_special = "__monad_sequence"
val monad_emptyseq_special = "__monad_emptyseq"
val monadassign_special = "__monad_assign"
val monad_bind = "monad_bind"
val monad_par = "monad_par"
val monad_return = "return"

val par_prec = 90
val ass_prec = 100

val genvar = "_%" (* impossible to type in as a variable; lexer splits it *)
fun is_genvar t = #2 (dest_var t) = oneSyntax.one_ty handle HOL_ERR _ => false

val _ = temp_add_listform {block_info = (PP.CONSISTENT,0),
                           cons = monadseq_special,
                           nilstr = monad_emptyseq_special,
                           leftdelim = [TOK "do", BreakSpace(1,2)],
                           rightdelim = [TOK "od"],
                           separator = [TOK ";", BreakSpace(1,0)]}

val _ = temp_add_rule {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
                       fixity = Infix(NONASSOC, ass_prec),
                       paren_style = OnlyIfNecessary,
                       pp_elements = [BreakSpace(1,0), TOK "<-", HardSpace 1],
                       term_name = monadassign_special}

val _ = temp_add_rule {block_style = (AroundSameName, (PP.INCONSISTENT, 2)),
                       fixity = Infix(RIGHT, par_prec),
                       paren_style = OnlyIfNecessary,
                       pp_elements = [BreakSpace(1,0), TOK "!!", HardSpace 1],
                       term_name = monad_par}

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

fun clean_action isolatedp a = let
  open Absyn
  val unit_pty = Pretype.Tyop{Args = [], Thy = "one", Tyop = "one"}
  fun mk_bare a = (VTYPED (locn.Loc_None,
                           VIDENT (locn.Loc_None, genvar),
                           unit_pty),
                   a)

in
  case a of
    APP(loc1, APP(loc2, IDENT(loc3, s), arg1), arg2) => let
    in
      if s = monadassign_special then
        if isolatedp then
          raise mk_HOL_ERRloc "parmonadsyntax" "clean_action" loc1
                              "Monad assign illegal in this position"
        else
          (to_vstruct arg1, clean_do false arg2)
      else if s = monad_par then let
          val (v1,a1) = clean_action isolatedp arg1
          val (v2,a2) = clean_action isolatedp arg2
        in
          (VPAIR(loc1,v1,v2),
           APP(loc1, APP(loc2, IDENT(loc3, s), a1), a2))
        end
      else mk_bare (clean_do true a)
    end
  | _ => mk_bare (clean_do true a)
end
and cleanseq a = let
  open Absyn
in
  case a of
    APP(loc1, APP(loc2, IDENT(loc3, s), arg1), arg2) => let
    in
      if s = monadseq_special then let
          val arg2' = clean_actions arg2
          val arg1_in = isSome arg2'
          val (bv, arg1') = clean_action (not arg1_in) arg1
        in
          case arg2' of
            NONE => SOME arg1'
          | SOME a => let
            in
              SOME (APP(loc1, APP(loc2,
                                  IDENT(loc3, monad_bind),
                                  arg1'),
                        LAM(locn_of_absyn a, bv, a)))
            end
        end
      else NONE
    end
  | _ => NONE
end
and clean_do isolatedp a = let
  open Absyn
  val isolated = clean_do true
  val clean_do = clean_do isolatedp
in
  case cleanseq a of
    SOME a => a
  | NONE => let
    in
      case a of
        APP(l,arg1 as APP(_,IDENT(_,s),_),arg2) =>
        if s = monad_par then
          if isolatedp then let
              val (vs, action) = clean_action true a
            in
              APP(l,
                  APP(locn.Loc_None,
                      IDENT(locn.Loc_None, monad_bind),
                      a),
                  LAM (locn.Loc_None,
                       vs,
                       APP(locn.Loc_None,
                           IDENT(locn.Loc_None, monad_return),
                           QIDENT(locn.Loc_None, "one", "one"))))
            end
          else APP(l,clean_do arg1, clean_do arg2)
        else
          APP(l,isolated arg1,isolated arg2)
      | APP(l,a1,a2) => APP(l,isolated a1, isolated a2)
      | LAM(l,v,a) => LAM(l,v,isolated a)
      | IDENT(loc,s) => if s = monad_emptyseq_special then
                          raise mk_HOL_ERRloc "monadsyntax" "clean_do" loc
                                              "Empty do-od pair illegal"
                        else a
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

val transform_absyn = clean_do true

val _ = Parse.temp_add_absyn_postprocessor ("monadsyntax.transform_absyn",
                                            transform_absyn)

fun prname G t = let
  val oinfo = term_grammar.overload_info G
in
  case Overload.overloading_of_term oinfo t of
    NONE => if is_var t then #1 (dest_var t)
            else raise term_pp_types.UserPP_Failed
  | SOME s => s
end

fun dest_binop s G t = let
  open term_pp_types
  val (fx, y) = dest_comb t
  val (f, x) = dest_comb fx
  val _ = prname G f = s orelse raise UserPP_Failed
in
  SOME (x, y)
end handle HOL_ERR _ => NONE
         | term_pp_types.UserPP_Failed =>  NONE

val dest_par = dest_binop monad_par
val dest_bind = dest_binop monad_bind


fun print_monads (tyg, tmg) sysprinter (ppfns:term_pp_types.ppstream_funs) (p,l,r) dpth pps t = let
  open term_pp_types term_grammar
  val (strn,brk) = (#add_string ppfns, #add_break ppfns);
  fun pbegin b = if b then strn "(" else ()
  fun pend b = if b then strn ")" else ()
  val (arg1, arg2) = valOf (dest_bind tmg t)
                             handle Option => raise UserPP_Failed
  fun pr_action (p,l,r) (vopt, action) = let
    fun atomic_assign () = let
      fun check_grav grav =
          case grav of
            Prec(n, _) => n > ass_prec
          | _ => false
      val bracketp = check_grav l orelse check_grav r
      val prec = Prec(ass_prec, monadassign_special)
      fun topify p = if bracketp then Top else p
    in
      pbegin bracketp;
      PP.begin_block pps PP.INCONSISTENT 0;
      sysprinter (prec, topify l, prec) (dpth - 1) (valOf vopt);
      strn " <-";
      brk(1,2);
      sysprinter (prec,prec,topify r) (dpth - 1) action;
      PP.end_block pps;
      pend bracketp
    end
  in
    case vopt of
      NONE => sysprinter (p,l,r) (dpth - 1) action
    | SOME v => let
      in
        case dest_par tmg action of
          NONE => let
          in
            if is_genvar v then sysprinter (p,l,r) (dpth - 1) action
            else atomic_assign()
          end
        | SOME (a1, a2) => let
          in
            case Lib.total pairSyntax.dest_pair v of
              NONE => atomic_assign()
            | SOME(v1, v2) => let
                fun check_grav a grav =
                    case grav of
                      Prec(n, _) => n > par_prec orelse (n = par_prec andalso
                                                         a <> RIGHT)
                    | _ => false
                val bracketp = check_grav RIGHT l orelse check_grav LEFT r
                fun topify p = if bracketp then Top else p
                val prec = Prec(par_prec, monad_par)
              in
                pbegin bracketp;
                PP.begin_block pps PP.INCONSISTENT 0;
                pr_action (prec,topify l,prec) (SOME v1, a1);
                strn " !!";
                brk(1,2);
                pr_action (prec,prec,topify r) (SOME v2, a2);
                PP.end_block pps;
                pend bracketp
              end
          end
      end
  end

  fun brk_bind arg1 arg2 = let
    val (v,body) = (SOME ## I) (pairSyntax.dest_pabs arg2)
                   handle HOL_ERR _ => (NONE, arg2)
  in
    ((v, arg1), body)
  end
  fun strip acc t =
      case dest_bind tmg t of
        NONE => List.rev ((NONE, t) :: acc)
      | SOME (arg1, arg2) => let
          val (arg1', arg2') = brk_bind arg1 arg2
        in
          strip (arg1'::acc) arg2'
        end
  val (arg1',arg2') = brk_bind arg1 arg2
  val actions = strip [arg1'] arg2'
  fun is_unit_return t = let
    val (f,x) = dest_comb t
  in
    prname tmg f = monad_return andalso
    type_of x = oneSyntax.one_ty
  end handle HOL_ERR _ => false | term_pp_types.UserPP_Failed => false
  val actions' = let
    fun laststuff [] = raise Fail "parmonadsyntax: inv failure"
      | laststuff [x] = raise Fail "parmonadsyntax: inv failure"
      | laststuff [(v1,bod1), (v2,bod2)] = (valOf v1, bod2)
      | laststuff (h::t) = laststuff t
    val (lastv, lastbody) = laststuff actions
  in
    if List.all is_genvar (pairSyntax.strip_pair lastv) andalso
       is_unit_return lastbody
    then
      #1 (Lib.front_last actions)
    else actions
  end
in
  if length actions' = 1 then sysprinter (p,l,r) dpth (#2 (hd actions'))
  else let
    in
      PP.begin_block pps PP.CONSISTENT 0;
        strn "do"; brk(1,2);
        Portable.pr_list (pr_action(Top,Top,Top))
                         (fn () => strn ";")
                         (fn () => brk(1,2))
                         actions';
        brk(1,0);
        strn "od";
      PP.end_block pps
    end
end

val _ = temp_add_user_printer ("parmonadsyntax.print_monads", ``x:'a``,
                               print_monads)


