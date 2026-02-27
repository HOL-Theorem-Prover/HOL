structure combinpp :> combinpp =
struct

open HolKernel boolLib Parse Absyn
val internal_consupd = "  combinpp.cons"
val internal_idupd = "  combinpp.nil"
val mapsto_special = "  combinpp.leftarrow"
val toplevel_updname = "  combinpp.top"

datatype dict_delta = DD of { left : string, right : string,
                              upd_term_name : term * string,
                              lookup_term_name : (term * string) option }
fun unicode_free_dd (DD {left, right, ...}) =
    not (UTF8.contains_nonascii left) andalso not (UTF8.contains_nonascii right)
datatype delta = ADD of dict_delta | RM of string

fun tstr_eq (t1,s1) (t2,s2) = s1 = s2 andalso t1 ~~ t2
fun opt_eq eq NONE NONE = true
  | opt_eq eq (SOME x) (SOME y) = eq x y
  | opt_eq eq _ _ = false

fun ddequal (DD dd1) (DD dd2) =
    #left dd1 = #left dd2 andalso #right dd1 = #right dd2 andalso
    tstr_eq (#upd_term_name dd1) (#upd_term_name dd2) andalso
    opt_eq tstr_eq (#lookup_term_name dd1) (#lookup_term_name dd2)

local open ThyDataSexp
in
val dded as (ddenc,dddec) = bij_ed (
      (fn DD {left=l,right=r,upd_term_name=utn,lookup_term_name=ltn} =>
          (l,r,utn,ltn)),
      (fn (l,r,utn,ltn) => DD {left = l, right = r, upd_term_name = utn,
                               lookup_term_name = ltn})
    ) (
      pair4_ed (
        string_ed, string_ed, pair_ed(term_ed, string_ed),
        option_ed(pair_ed (term_ed, string_ed))
      )
    )
val (delta_enc,delta_dec) = bij_ed (
      (fn ADD dd => inl dd | RM s => inr s),
      (fn inl dd => ADD dd | inr s => RM s)
    ) (tagged_sum ("add", dded) ("remove", string_ed))
end

type pppdb = {parse: dict_delta Symtab.table,
              print_upd: dict_delta list Symtab.table,
              print_lookup: dict_delta list Symtab.table}
val empty_pppdb : pppdb = {parse = Symtab.empty, print_upd = Symtab.empty,
                           print_lookup = Symtab.empty}

fun pppdb_apply_add
      (dd as DD{left,right,upd_term_name=utn,lookup_term_name=ltn})
      ({parse,print_upd,print_lookup} : pppdb) : pppdb =
    {parse = Symtab.update(left,dd) parse,
     print_upd = Symtab.update_list ddequal (#2 utn,dd) print_upd,
     print_lookup =
     case ltn of
         NONE => print_lookup
       | SOME(_,s) => Symtab.update_list ddequal (s,dd) print_lookup}

fun pppdb_apply_rm s {parse,print_upd,print_lookup} =
    let
      fun foldthis (p as (k, dds0)) tab0 =
          let val dds = List.filter (fn DD d => #left d = s) dds0
          in
            if null dds then tab0
            else Symtab.update (k,dds) tab0
          end
      fun rebuild tab0 = Symtab.fold foldthis tab0
    in
      {parse = Symtab.delete s parse handle Symtab.UNDEF _ => parse,
       print_upd = Symtab.build (rebuild print_upd),
       print_lookup = Symtab.build (rebuild print_lookup)}
    end

fun apply_delta (ADD dd) db = pppdb_apply_add dd db
  | apply_delta (RM s) db = pppdb_apply_rm s db

val pppdata_info = {
  tag = "dictppp", initial_values = [("min", empty_pppdb)],
  apply_delta = apply_delta
}
val {DB, record_delta, get_global_value, update_global_value,...} =
    AncestryData.fullmake {
      adinfo = pppdata_info,
      uptodate_delta = fn _ => true,
      sexps = {dec = delta_dec, enc = delta_enc},
      globinfo = {apply_to_global = apply_delta, thy_finaliser = NONE,
                  initial_value = empty_pppdb}
    }

fun ERR f l msg = Feedback.mk_HOL_ERRloc "combinpp" f l msg
fun cAPP l (a1, a2) = Absyn.APP(l,a1,a2)

fun gen_break_binop P f a =
    case a of
        APP(l, a1, a2) =>
          (case a1 of
               APP(l1, IDENT (l1', s), a12) =>
               if P s then SOME ((l, a12, a2), f s)
               else NONE
             | _ => NONE)
      | _ => NONE

fun break_binop ident a =
    Option.map #1 (gen_break_binop (fn s => s = ident) (fn s => s) a)

fun break_arrow a =
    case break_binop mapsto_special a of
        SOME(l, a1, a2) => SOME (a1,a2)
      | NONE => NONE

fun islistnil a_t =
    case a_t of
        IDENT (l, nm) => nm = internal_idupd
      | _ => false

fun process_updates (update_name, lookup_name_opt) f upds =
    if islistnil upds then f
    else
      case break_binop internal_consupd upds of
          SOME (l, arg1, arg2) =>
          let
          in
            case break_arrow arg1 of
                SOME (d,r) =>
                let
                  val t = process_updates (update_name, lookup_name_opt) f arg2
                in
                  cAPP l (
                    cAPP (locn.between(locn_of_absyn d)(locn_of_absyn r)) (
                      cAPP (locn_of_absyn d) (
                        IDENT (locn.Loc_None, update_name),
                        d
                      ),
                      r
                    ),
                    t
                  )
                end
              | NONE =>
                if islistnil arg2 then
                  case lookup_name_opt of
                      NONE => raise ERR "upd_processor" (locn_of_absyn upds)
                                    "Malformed update argument"
                    | SOME ln =>
                      cAPP l (cAPP l (IDENT (locn.Loc_None, ln), f), arg1)
                else
                  raise ERR "upd_processor" (locn_of_absyn arg1)
                        "Update list element should be update but isn't"
          end
        | NONE => raise ERR "upd_processor" (locn_of_absyn upds)
                        "Fn-update syntax update broken"

fun upd_processor0 (DB:pppdb) a =
    case a of
        LAM (l,v,a0) => LAM (l,v,upd_processor0 DB a0)
      | TYPED (l, a0, pty) => TYPED(l, upd_processor0 DB a0, pty)
      | APP(l,a1,a2) =>
        (case
            gen_break_binop
              (fn s => String.isPrefix toplevel_updname s)
              (fn s => String.extract(s, size toplevel_updname, NONE))
              a
           of
             NONE => APP(l, upd_processor0 DB a1, upd_processor0 DB a2)
           | SOME ((_, arg10, arg20), left) =>
             let
               val arg1 = upd_processor0 DB arg10
               val arg2 = upd_processor0 DB arg20
             in
               case Symtab.lookup(#parse DB) left of
                   NONE => raise ERR "upd_processor" (locn_of_absyn a)
                                 ("No stored info for " ^ left)
                 | SOME (DD {lookup_term_name, upd_term_name = (_, unm), ...}) =>
                   process_updates (unm, Option.map #2 lookup_term_name)
                                   arg1 arg2
             end)
      | _ => a

fun upd_processor G a = upd_processor0 (get_global_value()) a

val _ = term_grammar.userSyntaxFns.register_absynPostProcessor
          {name = "combin.UPDATE",
           code = upd_processor}

fun upd_printer (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm
    =
    let
      open term_pp_utils term_pp_types smpp
      val avoid_unicode = get_tracefn "PP.avoid_unicode" () = 1
      val oinfo = term_grammar.overload_info tmg
      fun oi_strip t =
          case Overload.oi_strip_comb oinfo t of
              SOME (f, [k,v,f0]) =>
              (case GrammarSpecials.dest_fakeconst_name (#1 (dest_var f)) of
                   SOME {fake, ...} => SOME (fake, (k,v), f0)
                 | _ => NONE)
            | _ => NONE
      val (updname, (k,v), next) =
          case oi_strip tm of SOME quad => quad | NONE => raise UserPP_Failed
      val {print_upd,...} = get_global_value()

      val candidate_dds =
          let val base = Symtab.lookup_list print_upd updname
          in
            if avoid_unicode then List.filter unicode_free_dd base
            else base
          end
      val (ld_s, rd_s) =
          case candidate_dds of
              [] => raise UserPP_Failed
            | DD d :: _ => (#left d, #right d)

      fun strip_upd t =
          let
            fun recurse A t =
                case oi_strip t of
                    SOME (u,(k,v),f) => if u = updname then
                                           recurse ((k,v)::A) f
                                         else (List.rev A, t)
                  | NONE => (List.rev A, t)
          in
            recurse [(k,v)] t
          end

      val (kvs, f) = strip_upd next
      val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs
      val arrow_s = if avoid_unicode then "|->" else "↦"
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
          {name = "combinpp.general_printer", code = upd_printer};

fun seln_printer  (tyg,tmg) backend printer ppfns (pgr,lgr,rgr) depth tm =
    let
      open term_pp_utils term_pp_types smpp
      val avoid_unicode = get_tracefn "PP.avoid_unicode" () = 1
      val oinfo = term_grammar.overload_info tmg
      fun oi_strip t =
          case Overload.oi_strip_comb oinfo t of
              SOME (f, [f0, k]) =>
              (case GrammarSpecials.dest_fakeconst_name (#1 (dest_var f)) of
                   SOME {fake, ...} => SOME (fake, f0, k)
                 | _ => NONE)
            | _ => NONE
      val (selname, f, k) =
          case oi_strip tm of SOME trip => trip | NONE => raise UserPP_Failed
      val {print_lookup,...} = get_global_value()

      val candidate_dds =
          let val base = Symtab.lookup_list print_lookup selname
          in
            if avoid_unicode then List.filter unicode_free_dd base
            else base
          end
      val (ld_s, rd_s) =
          case candidate_dds of
              [] => raise UserPP_Failed
            | DD d :: _ => (#left d, #right d)

      val {add_string,add_break,...} = ppfns : term_pp_types.ppstream_funs
      val paren =
          case lgr of
              Prec(i, _) => if i > 2100 then
                              fn p => block PP.INCONSISTENT 1 (
                                       add_string "(" >> p >>
                                       add_string ")"
                                     )
                            else (fn p => p)
            | _ => fn p => p
      val mygrav = case Parse.fixity ld_s of
                       SOME (term_grammar.Suffix i) => Prec(i, ld_s)
                     | _ => raise UserPP_Failed
    in
      paren (
        block PP.CONSISTENT 0 (
          printer {gravs = (pgr,lgr,mygrav), depth = decdepth depth,
                   binderp = false} f >>
          add_string ld_s >> add_break(0,2) >>
          printer {gravs = (Top,Top,Top),
                   depth = decdepth depth,
                   binderp = false} k >>
          add_break(0,0) >>
          add_string rd_s
        )
      )
    end

val _ = term_grammar.userSyntaxFns.register_userPP
          {name = "combinpp.seln_printer", code = seln_printer};

fun enable_dictsyntax () = (
      set_mapped_fixity {fixity = Infix(NONASSOC,100),
                         term_name = mapsto_special,
                         tok = "|->"};
      set_mapped_fixity {fixity = Infix(NONASSOC,100),
                         term_name = mapsto_special,
                         tok = "↦"};
      add_absyn_postprocessor "combin.UPDATE"
)

fun addlform l r =
    add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
              fixity = Suffix 2100,
              paren_style = OnlyIfNecessary,
              pp_elements = [
                TOK l,
                ListForm {
                  separator = [TOK ";", BreakSpace(1,0)],
                  block_info = (PP.CONSISTENT, 1),
                  cons = internal_consupd,
                  nilstr = internal_idupd
                },
                TOK r],
              term_name = toplevel_updname^l};

fun new_form (r as {left,right,upd_term_name = (updt,updnm), lookup_term_name}) =
    let
      val d = ADD (DD r)
    in
      addlform left right;
      record_delta d;
      update_global_value (apply_delta d);
      add_user_printer("combinpp.general_printer", updt);
      case lookup_term_name of
          NONE => ()
        | SOME (pat, nm) => add_user_printer("combinpp.seln_printer", pat)
    end

fun remove_paren_syntax lparen_name = (
  remove_termtok {tok = lparen_name, term_name = toplevel_updname ^ lparen_name};
  record_delta (RM lparen_name)
)

end (* struct *)
