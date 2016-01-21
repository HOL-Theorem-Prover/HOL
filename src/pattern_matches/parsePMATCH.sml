structure parsePMATCH :> parsePMATCH =
struct

exception unch
fun Unchanged a = raise unch
open term_grammar


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

fun mk_dtcase ar = map_tok_add_record (fn "case" => "dtcase" | s => s) ar
fun mk_pmcase ar = ar_name_fupd (K PMATCH_case_special) ar

fun add_pmatch get arule rmtmtok G =
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
        if do_pm then rmtmtok G {term_name = GrammarSpecials.core_case_special,
                                 tok = "case"}
        else G
    val G =
        if do_dtc then
          List.foldl (fn (ar, G) => arule G (mk_dtcase ar)) G crules
        else G
    val G =
        if do_pm then
          List.foldl (fn (ar, G) => arule G (mk_pmcase ar)) G crules
        else G
  in
    G
  end

val fixityRF = ar_fixity_fupd Parse.RF

val ADD_PMATCH =
    add_pmatch term_grammar
               (fn _ => Parse.add_rule o fixityRF)
               (fn _ => Parse.remove_termtok)

val temp_ADD_PMATCH =
    add_pmatch term_grammar
               (fn _ => Parse.temp_add_rule o fixityRF)
               (fn _ => Parse.temp_remove_termtok)

val grammar_add_pmatch =
    add_pmatch (fn g => g) term_grammar.add_rule remove_form_with_tok

(* ----------------------------------------------------------------------
    absyn traversal
   ---------------------------------------------------------------------- *)

open Absyn
fun optbind f x y k =
  case f x of
      NONE => (case f y of NONE => NONE
                         | SOME y' => SOME (k x y'))
    | SOME x' => (case f y of NONE => SOME (k x' y)
                            | SOME y' => SOME (k x' y'))

fun lift f x = case f x of NONE => x | SOME x' => x'

fun absyn_traverse (f : (absyn -> absyn option) -> absyn -> absyn option) =
  let
    fun recurse a =
      case f recurse a of
          NONE =>
          (case a of
               APP(l,a1,a2) => optbind recurse a1 a2
                                       (fn x => fn y => APP(l,x,y))
             | LAM(l,vs,a) => (case recurse a of NONE => NONE
                                               | SOME a' => SOME(LAM(l,vs,a')))
             | TYPED(l,a,pty) =>
                 (case recurse a of NONE => NONE
                                  | SOME a' => SOME(TYPED(l,a',pty)))
             | _ => NONE)
          | x => x
  in
    lift recurse
  end

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

fun mk_rowlist rs =
  case rs of
      [] => raise Fail "pmatch_case: impossible"
    | [r] =>
      let
        val l = locn_of_absyn r
      in
        APP(l,
            APP(l, QIDENT(noloc, "list", "CONS"), r),
            QIDENT(noloc, "list", "NIL"))
      end
    | r::rs =>
      let
        val l = locn_of_absyn r
      in
        APP(l,
            APP(l, QIDENT(noloc, "list", "CONS"), r),
            mk_rowlist rs)
      end

fun mk_row a =
  case a of
      APP(l1, APP(l2, IDENT (l3, arr), lh), rh) =>
      let
        val _ = arr = GrammarSpecials.case_arrow_special orelse
                raise mk_HOL_ERRloc "parsePMATCH" "pmatch_transform" l1
                      "No arrow"
      in
        APP(l1, APP(l2, IDENT (l3, ","), lh), rh)
      end
    | _ => raise mk_HOL_ERRloc "parsePMATCH" "pmatch_transform"
                 (locn_of_absyn a)
                 "No arrow"

fun pmatch_case recursor a =
  case a of
      APP(l1, APP(l2, IDENT(l3, c), arg1), arg2) =>
      if c = PMATCH_case_special then
        let
          val arg1 = lift recursor arg1
          val rows = map mk_row (strip_casesplit arg2)
        in
          SOME(APP(l1,APP(l2,QIDENT(l3,"patternMatches", "PMATCH"), arg1),
                   mk_rowlist rows))
        end
      else NONE
    | _ => NONE

val a = absyn_traverse pmatch_case (Absyn`case x of T => F | F => T`)


end
