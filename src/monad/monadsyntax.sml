structure monadsyntax :> monadsyntax =
struct

open HolKernel Parse boolLib
local open optionTheory in end

val monadseq_special = "__monad_sequence"
val monad_emptyseq_special = "__monad_emptyseq"
val monadassign_special = "__monad_assign"
val monadmlet_special = "__monad_mlet"
val monad_unitbind = "monad_unitbind"
val monad_bind = "monad_bind"
val mlet = "mlet"
val LET = "LET";

fun ERR f msg = mk_HOL_ERR "monadsyntax" f msg

type monadinfo = { bind : term,
                   ignorebind : term option,
                   unit : term,
                   fail : term option,
                   choice : term option,
                   guard : term option }

structure MonadInfo =
struct
  open ThyDataSexp
  type t = monadinfo
  fun toSexp {bind,ignorebind,unit,fail,choice,guard} =
      List [Term bind, Option (Option.map Term ignorebind),
            Term unit, Option (Option.map Term fail),
            Option (Option.map Term choice),
            Option (Option.map Term guard)]
  fun determOpt NONE = NONE
    | determOpt (SOME (Term t)) = SOME t
    | determOpt _ = raise ERR "fromSexp" "Expected term option"
  fun fromSexp s =
    case s of
        List [Term bind, Option ign_opt, Term unit, Option failopt,
              Option choiceopt, Option guardopt] =>
          {bind = bind, ignorebind = determOpt ign_opt, unit = unit,
           fail = determOpt failopt, guard = determOpt guardopt,
           choice = determOpt choiceopt}
      | _ => raise ERR "fromSexp"
                   "bad format - not an appropriately shaped list of 6 elements"
end

val monadDB =
    ref (Binarymap.mkDict String.compare : (string,MonadInfo.t) Binarymap.dict);

fun write_keyval (nm, mi) =
  let
    open ThyDataSexp
  in
    List [List [String nm, MonadInfo.toSexp mi]]
  end

fun load_from_disk {thyname, data} =
  let
    open ThyDataSexp
    fun dest_keyval (s : ThyDataSexp.t) : string * MonadInfo.t =
      case s of
          List [String key, mi_sexp] =>
            let
              val mit = MonadInfo.fromSexp mi_sexp
            in
              (key, mit)
            end
        | _ => raise ERR "load_from_disk" "keyval pair data looks bad"
  in
    case data of
        SOME (List keyvals) =>
          monadDB := List.foldl (fn ((k,v), acc) => Binarymap.insert(acc,k,v))
                                (!monadDB)
                                (map dest_keyval keyvals)
      | NONE => ()
      | _ => raise ERR "load_from_disk" "data looks bad"
  end

fun getMITname s =
  let
    open ThyDataSexp
  in
    case s of
        List [String k, _] => k
      | _ => raise ERR "getMITname" "Shouldn't happen"
  end

fun uptodate_check t =
  case t of
      ThyDataSexp.List tyis =>
      let
        val (good, bad) = partition ThyDataSexp.uptodate tyis
      in
        case bad of
            [] => NONE
          | _ =>
            let
              val tyinames = map getMITname bad
            in
              HOL_WARNING "monadsyntax" "uptodate_check"
                          ("Monad information for: " ^
                           String.concatWith ", " tyinames ^ " discarded");
              SOME (ThyDataSexp.List good)
            end
      end
    | _ => raise Fail "TypeBase.uptodate_check : shouldn't happen"


fun check_thydelta (t, tdelta) =
  let
    open TheoryDelta
  in
    case tdelta of
        NewConstant _ => uptodate_check t
      | NewTypeOp _ => uptodate_check t
      | DelConstant _ => uptodate_check t
      | DelTypeOp _ => uptodate_check t
      | _ => NONE
  end

val {export = export_minfo, ...} = ThyDataSexp.new{
      thydataty = "MonadInfoDB",
      load = load_from_disk, other_tds = check_thydelta,
      merge = ThyDataSexp.alist_merge
    }

fun predeclare (nm, t) = monadDB := Binarymap.insert(!monadDB, nm, t)
fun declare_monad p = (predeclare p; export_minfo (write_keyval p))

fun all_monads () = Binarymap.listItems (!monadDB)


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
    APP(_, APP(_, IDENT(_, s), arg1), arg2) => (
      if s = monadassign_special then
        case arg1 of
          APP (_, IDENT (_, s), arg3) =>
            if s = mlet then (SOME (to_vstruct arg3), true, arg2)
            else (SOME (to_vstruct arg1), false, arg2)
        | _ => (SOME (to_vstruct arg1), false, arg2)
      else if s = monadmlet_special then (SOME (to_vstruct arg1), true, arg2)
      else (NONE, false, a)
    )
  | _ => (NONE, false, a)
end

fun cleanseq a = let
  open Absyn
in
  case a of
    APP(loc1, APP(loc2, IDENT(loc3, s), arg1), arg2) => let
    in
      if s = monadseq_special then let
          val (bv, letm, arg1') = clean_action (clean_do true arg1)
          val arg2' = clean_actions arg2
        in
          case arg2' of
            NONE => if not letm then SOME arg1'
                    else raise mk_HOL_ERRloc "monadsyntax" "clean_seq" loc3
                              "Trailing mlet illegal"
          | SOME a => let
            in
              case bv of
                NONE => SOME (APP(loc1,
                                  APP(loc2,
                                      IDENT(loc3, monad_unitbind),
                                      arg1'),
                                  a))
              | SOME b =>
                  if not letm then SOME (APP(loc1,
                                    APP(loc2,
                                        IDENT(loc3, monad_bind),
                                        arg1'),
                                    LAM(locn_of_absyn a, b, a)))
                  else SOME (APP(loc1,
                                  APP(loc2,
                                      IDENT(loc3, LET),
                                      LAM(locn_of_absyn a, b, a)),
                                      arg1'))
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
        else if s = mlet andalso not indo then
          raise mk_HOL_ERRloc "monadsyntax" "clean_do" l
                              "Bare mlet illegal"
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

fun transform_absyn G a = clean_do false a



fun dest_bind G t = let
  open term_pp_types
  val oinfo = term_grammar.overload_info G
  val (f, args) = valOf (Overload.oi_strip_comb oinfo t)
                  handle Option => raise UserPP_Failed
  val (x,y) =
      case args of
          [x,y] => (x,y)
        | _ => raise UserPP_Failed
  val prname =
      f |> dest_var |> #1 |> GrammarSpecials.dest_fakeconst_name
        |> valOf |> #fake
        handle HOL_ERR _ => raise UserPP_Failed
             | Option => raise UserPP_Failed
  val _ = prname = monad_unitbind orelse
          (prname = monad_bind andalso pairSyntax.is_pabs y) orelse
          (prname = LET andalso pairSyntax.is_pabs x) orelse
           raise UserPP_Failed
in
  if prname = LET then SOME (prname, y, x) else SOME (prname, x, y)
end handle HOL_ERR _ => NONE
         | term_pp_types.UserPP_Failed =>  NONE


val explicit_mlets = ref false;

fun print_monads (tyg, tmg) backend sysprinter ppfns (p,l,r) depth t = let
  open term_pp_types term_grammar smpp term_pp_utils
  infix >>
  val ppfns = ppfns : ppstream_funs
  val {add_string=strn,add_break=brk,ublock,...} = ppfns
  val (prname, arg1, arg2) = valOf (dest_bind tmg t)
                             handle Option => raise UserPP_Failed
  val minprint = ppstring (#2 (print_from_grammars min_grammars))
  fun syspr bp gravs t =
    sysprinter {gravs = gravs, binderp = bp, depth = depth - 1} t
  fun pr_action (v, letm, action) =
      case (v, letm) of
        (NONE, _) => syspr false (Top,Top,Top) action
      | (SOME v, false) => let
          val new_bvars = free_vars v
        in
          ublock PP.INCONSISTENT 0
            (record_bvars new_bvars
                          (syspr true (Top,Top,Prec(100, "monad_assign")) v) >>
             strn " " >> strn "<-" >> brk(1,2) >>
             syspr false (Top,Prec(100, "monad_assign"),Top) action) >>
          addbvs new_bvars
        end
      | (SOME v, true) => let
          val new_bvars = free_vars v
        in
          if !explicit_mlets then
            ublock PP.INCONSISTENT 0
              (strn mlet >>
               record_bvars new_bvars
                  (syspr true (Top,Top,Prec(100, "monad_assign")) v) >>
               strn " " >> strn "<-" >> brk(1,2) >>
               syspr false (Top,Prec(100, "monad_assign"),Top) action) >>
            addbvs new_bvars
          else
            ublock PP.INCONSISTENT 0
              (record_bvars new_bvars
                  (syspr true (Top,Top,Prec(100, "monad_assign")) v) >>
               strn " " >> strn "<<-" >> brk(1,2) >>
               syspr false (Top,Prec(100, "monad_assign"),Top) action) >>
            addbvs new_bvars
        end
  fun brk_bind binder arg1 arg2 =
      if binder = monad_bind orelse binder = LET then let
              val (v,body) = (SOME ## I) (pairSyntax.dest_pabs arg2)
                             handle HOL_ERR _ => (NONE, arg2)
        in
          ((v, binder = LET, arg1), body)
        end
      else ((NONE, false, arg1), arg2)
  fun strip acc t =
      case dest_bind tmg t of
        NONE => List.rev ((NONE, false, t) :: acc)
      | SOME (prname, arg1, arg2) => let
          val (arg1', arg2') = brk_bind prname arg1 arg2
        in
          strip (arg1'::acc) arg2'
        end
  val (arg1',arg2') = brk_bind prname arg1 arg2
  val actions = strip [arg1'] arg2'
  fun pr_action_list _ [] = []
    | pr_action_list 0 _ = [strn "..."]
    | pr_action_list print_length (b::bs) =
        pr_action b :: pr_action_list (decdepth print_length) bs
  fun concatWith brk [] = nothing
    | concatWith brk [x] = x
    | concatWith brk (x::xs) =
        let fun mk [] = nothing
              | mk (y::ys) = brk >> y >> mk ys
        in x >> mk xs end
in
  ublock PP.CONSISTENT 0
    (strn "do" >> brk(1,2) >>
     getbvs >- (fn oldbvs =>
     concatWith (strn ";" >> brk(1,2))
      (pr_action_list (!Globals.max_print_length) actions) >>
     brk(1,0) >>
     strn "od" >> setbvs oldbvs))
end

val _ = term_grammar.userSyntaxFns.register_userPP {
          name = "monadsyntax.print_monads",
          code = print_monads
    }
val _ = term_grammar.userSyntaxFns.register_absynPostProcessor {
          name = "monadsyntax.transform_absyn",
          code = transform_absyn
    }

fun syntax_actions al ar aup app = (
   al {block_info = (PP.CONSISTENT,0),
       cons = monadseq_special,
       nilstr = monad_emptyseq_special,
       leftdelim = [TOK "do", BreakSpace(1,2)],
       rightdelim = [TOK "od"],
       separator = [TOK ";", BreakSpace(1,0)]};
   ar {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
       fixity = Infix(NONASSOC, 100),
       paren_style = OnlyIfNecessary,
       pp_elements = [BreakSpace(1,0), TOK "<-", HardSpace 1],
       term_name = monadassign_special};
   ar {block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
       fixity = Infix(NONASSOC, 100),
       paren_style = OnlyIfNecessary,
       pp_elements = [BreakSpace(1,0), TOK "<<-", HardSpace 1],
       term_name = monadmlet_special};
   aup ("monadsyntax.print_monads", mk_var("x", alpha), print_monads);
   app ("monadsyntax.transform_absyn", transform_absyn)
   )

fun temp_add_monadsyntax () =
    syntax_actions temp_add_listform temp_add_rule temp_add_user_printer
                   temp_add_absyn_postprocessor

val monad_lform_name =
    GrammarSpecials.mk_lform_name {
      cons = monadseq_special,
      nilstr = monad_emptyseq_special
    }

fun mk_unitbind mbind =
  let
    val (m1ty, rng) = dom_rng (type_of mbind)
    val (fm2ty, m2ty) = dom_rng rng
    val (argty, _) = dom_rng fm2ty
    val m1 = mk_var("m1", m1ty)
    val m2 = mk_var("m2", m2ty)
    val K  = combinSyntax.K_tm |> inst [alpha |-> type_of m2, beta |-> argty]
    val Km2= mk_comb(K, m2)
  in
    list_mk_abs([m1,m2], list_mk_comb(mbind, [m1, Km2]))
  end

fun getMI fname s =
  case Binarymap.peek(!monadDB, s) of
      NONE => raise ERR fname ("No such monad defined: "^s)
    | SOME mi => mi

(* iovl is used so that fail and return don't contaminate normal uses *)
fun gen_enable_monad fname iovl ovl s =
  let
    val {bind,ignorebind,unit,fail,choice,guard} = getMI fname s
  in
    ovl ("monad_bind", bind);
    ovl ("monad_unitbind",
         case ignorebind of NONE => mk_unitbind bind | SOME ib => ib);
    iovl ("return", unit) ;
    Option.app (fn f => iovl("fail", f)) fail;
    Option.app (fn c => ovl("++", c)) choice;
    Option.app (fn g => ovl("assert", g)) guard
  end

fun gen_disable_monad fname rmovl s =
  let
    val {bind,ignorebind,unit,fail,choice,guard} = getMI fname s
  in
    rmovl "monad_bind" bind;
    rmovl "monad_unitbind"
          (case ignorebind of NONE => mk_unitbind bind | SOME ib => ib);
    rmovl "return" unit;
    Option.app (rmovl "fail") fail;
    Option.app (rmovl "++") choice;
    Option.app (rmovl "assert") guard
  end

fun gen_inferior_overload_on raw (s, t) =
  (* want to have t still print with monad syntax, just don't want this to be
     preferred target when parsing.  So, have to make sure that this ranks
     higher than the raw name of the constant *)
  (raw (s, t);
   if is_const t then
     let
       val G = term_grammar()
       val {Name,...} = dest_thy_const t
       val oinfo = term_grammar.overload_info G
       val ms = Overload.PrintMap.match (Overload.raw_print_map oinfo, t)
     in
       if List.exists (fn (_, (_, s, _)) => s = Name) ms then
         raw (Name, t)
       else ()
     end
   else ())

val enable_monad =
    gen_enable_monad "enable_monad" inferior_overload_on overload_on
val weak_enable_monad =
    gen_enable_monad "weak_enable_monad"
                     inferior_overload_on
                     (gen_inferior_overload_on inferior_overload_on)
val disable_monad = gen_disable_monad "disable_monad" gen_remove_ovl_mapping
val temp_weak_enable_monad =
    gen_enable_monad "temp_weak_enable_monad"
                     temp_inferior_overload_on
                     (gen_inferior_overload_on temp_inferior_overload_on)
val temp_enable_monad =
    gen_enable_monad "temp_enable_monad"
                     temp_inferior_overload_on
                     temp_overload_on
val temp_disable_monad =
    gen_disable_monad "temp_disable_monad" temp_gen_remove_ovl_mapping

fun gen_disable_syntax rr rup rpp =
  (rr {term_name = monad_lform_name, tok = "do"};
   rr {term_name = monadassign_special, tok = "<-"};
   rr {term_name = monadmlet_special, tok = "<<-"};
   rup "monadsyntax.print_monads";
   rpp "monadsyntax.transform_absyn")

fun disable_monadsyntax () =
  gen_disable_syntax remove_termtok remove_user_printer (fn s => ())
fun temp_disable_monadsyntax () =
  gen_disable_syntax temp_remove_termtok temp_remove_user_printer (fn s => ())

fun aup (s, pat, code) = (add_ML_dependency "monadsyntax";
                          add_user_printer (s, pat))

fun aap (s, code) = (add_ML_dependency "monadsyntax";
                     add_absyn_postprocessor s)

fun add_monadsyntax () = syntax_actions add_listform add_rule aup aap

val enable_monadsyntax = add_monadsyntax
val temp_enable_monadsyntax = temp_add_monadsyntax

fun print_explicit_monadic_lets b = (explicit_mlets := b);

val _ = TexTokenMap.temp_TeX_notation
            {hol = "<-", TeX = ("\\HOLTokenLeftmap{}", 1)}
val _ = TexTokenMap.temp_TeX_notation {hol = "do", TeX = ("\\HOLKeyword{do}", 2)}
val _ = TexTokenMap.temp_TeX_notation {hol = "od", TeX = ("\\HOLKeyword{od}", 2)}

val _ = predeclare (
      "option",
      { bind = prim_mk_const {Name = "OPTION_BIND", Thy = "option"},
        ignorebind = SOME (prim_mk_const{
                              Name = "OPTION_IGNORE_BIND", Thy = "option"}),
        unit = prim_mk_const {Name = "SOME", Thy = "option"},
        fail = SOME (prim_mk_const {Name = "NONE", Thy = "option"}),
        guard = SOME (prim_mk_const {Name = "OPTION_GUARD", Thy = "option"}),
        choice = SOME (prim_mk_const {Name = "OPTION_CHOICE", Thy = "option"})
      });

end (* struct *)
