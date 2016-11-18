structure parsePMATCH :> parsePMATCH =
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
                    fixity : term_grammar.fixity,
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

fun case_rules s ((precopt, r : grammar_rule),acc) : add_record list
  =
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


(* ----------------------------------------------------------------------
    pmatch absyn to preterm-in-env conversion
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
fun push bvs = fupd_scope (fn s => bvs @ s)
fun popn n = fupd_scope (fn s => List.drop(s,n))

fun ptlist_mk_comb [] = raise Fail "ptlist_mk_comb: empty list"
  | ptlist_mk_comb [t] = t
  | ptlist_mk_comb (f::x::xs) =
    ptlist_mk_comb (Preterm.Comb{Locn = noloc, Rand = x, Rator = f} :: xs)

val UNCURRY_pty = Pretype.fromType (type_of pairSyntax.uncurry_tm)
open Preterm errormonad
val mkUNCURRY =
    lift (fn pty => Const {Locn=noloc, Name="UNCURRY", Thy="pair", Ty=pty})
         (Pretype.rename_typevars [] UNCURRY_pty)

fun ptmkabs((vnm,vty),b) =
  Abs{Body = b, Bvar = Preterm.Var{Locn=noloc,Name=vnm,Ty=vty}, Locn = noloc}
fun ptmkcomb(f,x) = Preterm.Comb{Rator = f, Rand = x, Locn = noloc}
fun tuplify vs body =
  case vs of
      [] => return body
    | [x] => return (ptmkabs(x,body))
    | [x,y] => lift (fn pt => ptmkcomb(pt, ptmkabs(x,ptmkabs(y,body))))
                    mkUNCURRY
    | v::rest => lift2 (fn body' => fn pt => ptmkcomb(pt, ptmkabs(v, body')))
                       (tuplify rest body)
                       mkUNCURRY

val pty_to_string = PP.pp_to_string 70 Pretype.pp_pretype
(*
fun envdiag msg E = ()
  print (msg ^ ": " ^
         String.concatWith ", "
                           (map (fn (n,ty) => n ^ ": " ^ pty_to_string ty)
                                (frees E)) ^ "\n") *)

fun extract_fvs ptm =
  let
    open Preterm Pretype
    fun recurse tyopt acc ptm =
      case (ptm, tyopt) of
          (Var{Name,Ty,...}, NONE) => return ((Name, Ty) :: acc)
        | (Var{Name,...}, SOME Ty) => return ((Name, Ty) :: acc)
        | (Constrained {Ptm,Ty,...}, _) => recurse (SOME Ty) acc Ptm
        | (Comb{Rator = Comb{Rator = Const {Name = ",", Thy = "pair", ...},
                             Rand = arg1, ...},
                Rand = arg2, ...}, _) =>
          (case tyopt of
               SOME (Tyop{Thy = "pair", Tyop = "prod", Args = [ty1,ty2]}) =>
                 recurse (SOME ty2) acc arg2 >-
                 (fn a => recurse (SOME ty1) a arg1)
             | _ => recurse NONE acc arg2 >- (fn a => recurse NONE a arg1))
        | (Comb{Rator = arg1, Rand = arg2, ...}, _) =>
             recurse NONE acc arg2 >- (fn a => recurse NONE a arg1)
        | (Antiq{Tm,...}, _) =>
            term_to_preterm [] Tm >-
            (fn pt => recurse (SOME (fromType (type_of Tm))) acc pt)
        | _ => return acc
  in
    recurse NONE [] ptm
  end

fun update_ptyE (old:env) = fupd_ptyE (K (#ptyE old))

fun mk_row recursor a E =
  case a of
      APP(l1, APP(l2, IDENT (l3, arr), lh), rh) =>
      let
        (* val _ = envdiag "mk_row entry" E *)
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
              | SOME a =>
                let
                  val (bv_ptm, E') = recursor a (update_ptyE E empty_env)
                in
                  SOME (smash (extract_fvs bv_ptm) (#ptyE E'), E')
                end

        val (patStartE,pop_count) =
            case bvsE of
                NONE => (update_ptyE E empty_env,0)
              | SOME (vs,bv_env) => (push vs (update_ptyE bv_env E), length vs)

        val (pat_ptm, patfrees, patE0) =
            let
              val (pat_ptm, E') = recursor pat patStartE
            in
              (pat_ptm,
               Lib.set_diff (frees E') (frees patStartE),
               popn pop_count E')
            end
        val (allvars0, patE) =
            case bvsE of
                NONE => (List.rev patfrees, update_ptyE patE0 E)
              | SOME (vs, _) =>
                (vs @ List.filter (fn(nm,_) => String.isPrefix "_" nm) patfrees,
                 patE0)
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
        val (prow_pt,penultE) = PMATCH_ROW_pt rhE
        val tupled_argsM = mmap (tuplify allvars) [pat_ptm, guard_ptm, rh_ptm]
        val (tupled_args, ptyE) =
            case tupled_argsM (#ptyE penultE) of
                Some(ptyE', pts) => (pts, ptyE')
              | Error e => raise mkExn e
        (* val _ = envdiag "mk_row exit" rhE *)
      in
        (ptlist_mk_comb (prow_pt :: tupled_args), fupd_ptyE (K ptyE) penultE)
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

(* ----------------------------------------------------------------------
    Functions to modify grammars so that they do or don't use new
    pmatch case expressions
  ---------------------------------------------------------------------- *)

fun add_pmatch actions (G:'a) =
  let
    val {get, arule : add_record -> 'a -> 'a, rmtmtok,
         add_ptmproc: string * int -> preterm_processor -> 'a -> 'a,
         addup, up} =
        actions
    val crules = grammar_tok_rules "case" (get G)
    val dtcrules0 = grammar_tok_rules "dtcase" (get G)
    val do_dtc = null dtcrules0
    val do_pm =
        case crules of
            [] => raise mk_HOL_ERR "parsePMATCH" "ADD_PMATCH"
                        "No existing case rules?"
          | c :: _ => #term_name c <> PMATCH_case_special
    val _ = set_trace "pp_cases_dt" 1
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
    val G = if do_pm then
              G |> add_ptmproc (PMATCH_case_special, 2) pmatch_case
            else G
    val G = if do_pm then G |> addup up else G
  in
    G
  end



end
