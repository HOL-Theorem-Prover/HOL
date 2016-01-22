structure parsePMATCH =
struct

open Lib HolKernel Parse term_grammar

fun case_element s (e : pp_element) =
  case e of
      RE (TOK s') => s = s'
    | PPBlock(els,_) => case_elements s els
    | _ => false
and case_elements s (els : pp_element list) = List.exists (case_element s) els

fun case_rulerecord s fixity (rr : rule_record, acc) =
  let
    val {block_style,elements,paren_style,term_name,...} = rr
  in
    if case_elements s elements then
      {block_style = block_style, fixity = fixity,
       paren_style = paren_style, pp_elements = elements,
       term_name = term_name} :: acc
    else acc
  end

type add_record = { block_style : PhraseBlockStyle * block_info,
                    fixity : rule_fixity,
                    paren_style : ParenStyle,
                    pp_elements : pp_element list,
                    term_name : string }
fun ar_elements_fupd
      f
      ({block_style,fixity,paren_style,pp_elements,term_name} : add_record) =
  { block_style = block_style, fixity = fixity, paren_style = paren_style,
    pp_elements = f pp_elements, term_name = term_name }
fun ar_name_fupd
      (f : string -> string)
      ({block_style,fixity,paren_style,pp_elements,term_name} : add_record) =
  { block_style = block_style, fixity = fixity, paren_style = paren_style,
    pp_elements = pp_elements, term_name = f term_name }
fun ar_fixity_fupd
      (f : rule_fixity -> 'a)
      ({block_style,fixity,paren_style,pp_elements,term_name} : add_record) =
  { block_style = block_style, fixity = f fixity, paren_style = paren_style,
    pp_elements = pp_elements, term_name = term_name }

fun case_rules s ((precopt, r : grammar_rule),acc) : add_record list =
  case (precopt, r) of
      (_, CLOSEFIX rrs) =>
        List.foldl (case_rulerecord s Closefix) acc rrs
    | (SOME prec, INFIX (STD_infix (rrs, ass))) =>
        List.foldl (case_rulerecord s (Infix(ass,prec))) acc rrs
    | (SOME prec, PREFIX (STD_prefix rrs)) =>
        List.foldl (case_rulerecord s (Prefix prec)) acc rrs
    | (SOME prec, SUFFIX (STD_suffix rrs)) =>
        List.foldl (case_rulerecord s (Suffix prec)) acc rrs
    | _ => acc

fun grammar_tok_rules tok G = List.foldl (case_rules tok) [] (rules G)

fun map_tok_element f e =
  case e of
      RE (TOK s) => RE (TOK (f s))
    | PPBlock(els, bi) => PPBlock(map_tok_elements f els, bi)
    | _ => e
and map_tok_elements f els = map (map_tok_element f) els

fun map_tok_add_record f = ar_elements_fupd (map_tok_elements f)

val PMATCH_case_special = GrammarSpecials.mk_case_special "PMATCH"
val PMATCH_endbinding =
    GrammarSpecials.mk_fakeconst_name {fake = ".|",
                                       original = SOME{Thy = "patternMatches",
                                                       Name = "endbinding"}}
val PMATCH_when =
    GrammarSpecials.mk_fakeconst_name {fake = "when",
                                       original = SOME{Thy = "patternMatches",
                                                       Name = "when"}}

val endbinding_ar = {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                     fixity = Infix(NONASSOC, 13),
                     paren_style = OnlyIfNecessary,
                     pp_elements = [RE (TOK ".|")],
                     term_name = PMATCH_endbinding}
val when_ar = {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
               fixity = Infix(NONASSOC, 14),
               paren_style = OnlyIfNecessary,
               pp_elements = [RE (TOK "when")],
               term_name = PMATCH_when}

fun mk_dtcase ar = map_tok_add_record (fn "case" => "dtcase" | s => s) ar
fun mk_pmcase ar = ar_name_fupd (K PMATCH_case_special) ar

fun add_pmatch get (arule : add_record -> 'a -> 'a) rmtmtok G =
  let
    val crules = grammar_tok_rules "case" (get G)
    val dtcrules0 = grammar_tok_rules "dtcase" (get G)
    val do_dtc = null dtcrules0
    val do_pm =
        case crules of
            [] => raise mk_HOL_ERR "parsePMATCH" "ADD_PMATCH"
                        "No existing case rules?"
          | c :: _ => #term_name c <> PMATCH_case_special
    val G =
        if do_pm then rmtmtok {term_name = GrammarSpecials.core_case_special,
                               tok = "case"} G
        else G
    val G =
        if do_dtc then
          List.foldl (fn (ar, G) => arule (mk_dtcase ar) G) G crules
        else G
    val G =
        if do_pm then
          List.foldl (fn (ar, G) => arule (mk_pmcase ar) G) G crules
        else G
    val G = if do_pm then
              G |> arule when_ar |> arule endbinding_ar
            else G
  in
    G
  end

val fixityRF = ar_fixity_fupd Parse.RF

val ADD_PMATCH =
    add_pmatch term_grammar
               (K o Parse.add_rule o fixityRF)
               (K o Parse.remove_termtok)

val temp_ADD_PMATCH =
    add_pmatch term_grammar
               (K o Parse.temp_add_rule o fixityRF)
               (K o Parse.temp_remove_termtok)

val grammar_add_pmatch =
    add_pmatch (fn g => g) (C term_grammar.add_rule) (C remove_form_with_tok)

(* ----------------------------------------------------------------------
    absyn traversal
   ---------------------------------------------------------------------- *)

open Absyn Parse_support Parse_supportENV

fun strip_casesplit a =
  let
    fun recurse acc a =
      case a of
          APP(_, APP(_, QIDENT(_, "bool", csplit), a1), a2) =>
            if csplit = GrammarSpecials.case_split_special then
              recurse (recurse acc a2) a1
            else
              a::acc
        | _ => a::acc
  in
    recurse [] a
  end

val noloc = locn.Loc_None
val cons_pt = Parse_support.make_qconst noloc ("list", "CONS")
val nil_pt = Parse_support.make_qconst noloc ("list", "NIL")
val PMATCH_ROW_pt =
    Parse_support.make_qconst noloc ("patternMatches", "PMATCH_ROW")
val unit_pty = Pretype.Tyop{Thy = "one", Tyop = "one", Args = []}
val bool_pty = Pretype.Tyop{Thy = "min", Tyop = "bool", Args = []}

fun mk_ptlist pts =
  case pts of
      [] => nil_pt
    | h::t => Parse_support.list_make_comb noloc [cons_pt, h, mk_ptlist t]

type env = Parse_supportENV.env
fun push bvs ({scope,free,uscore_cnt} : env) : env =
  {scope = bvs @ scope, free = free, uscore_cnt = uscore_cnt}

fun popn n ({scope,free,uscore_cnt} : env) : env =
  {scope = List.drop(scope,n), free = free, uscore_cnt = uscore_cnt}

fun ptlist_mk_comb [] = raise Fail "ptlist_mk_comb: empty list"
  | ptlist_mk_comb [t] = t
  | ptlist_mk_comb (f::x::xs) =
    ptlist_mk_comb (Preterm.Comb{Locn = noloc, Rand = x, Rator = f} :: xs)

val UNCURRY_pty = Pretype.fromType (type_of pairSyntax.uncurry_tm)
fun mkUNCURRY () =
  Preterm.Const {Locn = noloc, Name = "UNCURRY", Thy = "pair",
                 Ty = Pretype.rename_typevars [] UNCURRY_pty}

fun ptmkabs((vnm,vty),b) =
  Preterm.Abs{Body = b,
              Bvar = Preterm.Var{Locn=noloc,Name=vnm,Ty=vty},
              Locn = noloc}
fun ptmkcomb(f,x) = Preterm.Comb{Rator = f, Rand = x, Locn = noloc}
fun tuplify vs body =
  case vs of
      [] => body
    | [x] => ptmkabs(x,body)
    | [x,y] => ptmkcomb(mkUNCURRY(), ptmkabs(x,ptmkabs(y,body)))
    | v::rest => ptmkcomb(mkUNCURRY(), ptmkabs(v, tuplify rest body))

fun mk_row recursor a E =
  case a of
      APP(l1, APP(l2, IDENT (l3, arr), lh), rh) =>
      let
        val _ = arr = GrammarSpecials.case_arrow_special orelse
                raise mk_HOL_ERRloc "parsePMATCH" "pmatch_transform" l1
                      "No arrow"
        val (bvs_opt, lhbody) =
            case lh of
                APP(_, APP(_, IDENT (_, bvsplit), bvs), body) =>
                  if bvsplit = PMATCH_endbinding then (SOME bvs, body)
                  else (NONE, lh)
              | _ => (NONE, lh)
        val (pat, guard_opt) =
            case lhbody of
                APP(_, APP(_, IDENT(_, gdsplit), pat), gd) =>
                  if gdsplit = PMATCH_when then
                    (pat, SOME gd)
                  else (lhbody, NONE)
              | _ => (lhbody, NONE)
        val bvsE =
            case bvs_opt of
                NONE => NONE
              | SOME a => recursor a empty_env |> #2 |> SOME
        val (patStartE,pop_count) =
            case bvsE of
                NONE => (empty_env,0)
              | SOME e => let val vs = frees e in (push vs E, length vs) end

        val (pat_ptm, patfrees, patE) =
            let
              val (pat_ptm, E') = recursor pat patStartE
            in
              (pat_ptm,
               Lib.set_diff (frees E') (frees E),
               popn pop_count E')
            end
        val allvars0 =
            case bvsE of
                NONE => patfrees
              | SOME e => List.filter (fn (nm,_) => String.isPrefix "_" nm)
                                      patfrees @
                          frees e
        val allvars = if null allvars0 then [("_", unit_pty)] else allvars0
        val allpop_count = length allvars
        val (guard_ptm, guardE) =
            case guard_opt of
                NONE => (Preterm.Const{Thy="bool", Name = "T", Locn = noloc,
                                       Ty = bool_pty}, patE)
              | SOME ga =>
                let
                  val (g, E') = recursor ga (push allvars patE)
                in
                  (g, popn allpop_count E')
                end
        val (rh_ptm, rhE) = let
          val (pt, E') = recursor rh (push allvars guardE)
        in
          (pt, popn allpop_count E')
        end
        val (prow_pt,_) = PMATCH_ROW_pt rhE
        val tupled_args =
            map (tuplify (List.rev allvars)) [pat_ptm, guard_ptm, rh_ptm]
      in
        (ptlist_mk_comb (prow_pt :: tupled_args), rhE)
      end
    | _ => raise mk_HOL_ERRloc "parsePMATCH" "pmatch_transform"
                 (locn_of_absyn a)
                 "No arrow"

fun pmatch_case G recursor a =
  case a of
      APP(l1, APP(l2, IDENT(l3, c), arg1), arg2) =>
      let
        open Parse_support
        val arg1 = recursor arg1
        val pmatch_pt = make_qconst noloc ("patternMatches", "PMATCH")
        val rows = map (mk_row recursor) (strip_casesplit arg2)
      in
        list_make_comb l1 [pmatch_pt, arg1, mk_ptlist rows]
      end
    | _ => raise Fail "pmatch_case: should never happen"

end
