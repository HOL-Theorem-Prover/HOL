open HOLgrammars GrammarSpecials

  type block_info = PP.break_style * int
  datatype rule_element = TOK of string | TM
  datatype pp_element =
    PPBlock of pp_element list * block_info |
    EndInitialBlock of block_info | BeginFinalBlock of block_info |
    HardSpace of int | BreakSpace of (int * int) |
    RE of rule_element | LastTM | FirstTM
  (* these last two only used internally *)

    datatype PhraseBlockStyle =
      AroundSameName | AroundSamePrec | AroundEachPhrase
    datatype ParenStyle =
      Always | OnlyIfNecessary | ParoundName | ParoundPrec

  fun rule_elements0 acc pplist =
    case pplist of
      [] => acc
    | ((RE x) :: xs) => rule_elements0 (acc @ [x]) xs
    | (PPBlock(pels, _) :: xs) => rule_elements0 (rule_elements0 acc pels) xs
    | ( _ :: xs) => rule_elements0 acc xs
  val rule_elements = rule_elements0 []


  fun rels_ok [TOK _] = true
    | rels_ok (TOK _ :: TM :: xs) = rels_ok xs
    | rels_ok (TOK _ :: xs) = rels_ok xs
    | rels_ok _ = false

  fun pp_elements_ok pplist = let
    fun check_em toplevel eibs_ok els =
      case els of
        [] => true
      | (x::xs) => let
        in
          case x of
            LastTM => false
          | FirstTM => false
          | EndInitialBlock _ =>
              toplevel andalso eibs_ok andalso check_em true true xs
          | BeginFinalBlock _ => toplevel andalso check_em true false xs
          | PPBlock(els, _) =>
              check_em false false els andalso check_em toplevel eibs_ok xs
          | _ => check_em toplevel eibs_ok xs
        end
  in
    rels_ok (rule_elements pplist) andalso check_em true true pplist
  end




fun reltoString (TOK s) = s
  | reltoString TM = "TM"

type rule_record = {term_name : string,
                    elements : pp_element list,
                    preferred : bool,
                    block_style : PhraseBlockStyle * block_info,
                    paren_style : ParenStyle}

fun update_rr_pref b
  {term_name, elements, preferred, block_style, paren_style} =
  {term_name = term_name, elements = elements, preferred = b,
   block_style = block_style, paren_style = paren_style}

datatype binder = LAMBDA | BinderString of string
datatype prefix_rule = STD_prefix of rule_record list | BINDER of binder list
datatype suffix_rule = STD_suffix of rule_record list | TYPE_annotation
datatype infix_rule =
  STD_infix of rule_record list * associativity |
  RESQUAN_OP

type listspec =
  {separator : string, leftdelim : string, rightdelim : string,
   cons : string, nilstr : string}

datatype grammar_rule =
  PREFIX of prefix_rule
| SUFFIX of suffix_rule
| INFIX of infix_rule
| CLOSEFIX of rule_record list
| FNAPP | VSCONS
| LISTRULE of listspec list

type overload_info = Overload.overload_info

type grammar = {rules : (int option * grammar_rule) list,
                specials : {type_intro : string,
                            lambda : string,
                            endbinding : string,
                            restr_binders : (binder * string) list,
                            res_quanop : string},
                numeral_info : (char * string option) list,
                overload_info : overload_info}

fun specials (G: grammar) = #specials G
fun numeral_info (G: grammar) = #numeral_info G
fun overload_info (G: grammar) = #overload_info G

fun fupdate_rules f {rules, specials, numeral_info, overload_info} =
  {rules = f rules, specials = specials, numeral_info = numeral_info,
   overload_info = overload_info}
fun fupdate_specials f {rules, specials, numeral_info, overload_info} =
  {rules = rules, specials = f specials, numeral_info = numeral_info,
   overload_info = overload_info}
fun fupdate_numinfo f {rules, specials, numeral_info, overload_info} =
  {rules = rules, specials = specials, numeral_info = f numeral_info,
   overload_info = overload_info}
fun fupdate_overload_info f {rules, specials, numeral_info, overload_info} =
  {rules = rules, specials = specials, numeral_info = numeral_info,
   overload_info = f overload_info}

fun update_restr_binders rb
  {lambda, endbinding, type_intro, restr_binders, res_quanop} =
  {lambda = lambda, endbinding = endbinding, type_intro = type_intro,
   restr_binders = rb, res_quanop = res_quanop}

fun fupdate_restr_binders f
  {lambda, endbinding, type_intro, restr_binders, res_quanop} =
  {lambda = lambda, endbinding = endbinding, type_intro = type_intro,
   restr_binders = f restr_binders, res_quanop = res_quanop}

fun map_rrfn_rule f r =
  case r of
    PREFIX (STD_prefix rlist) => PREFIX (STD_prefix (map f rlist))
  | PREFIX (BINDER _) => r
  | INFIX (STD_infix (rlist, a)) => INFIX (STD_infix (map f rlist, a))
  | INFIX RESQUAN_OP => r
  | SUFFIX (STD_suffix rlist) => SUFFIX (STD_suffix (map f rlist))
  | SUFFIX TYPE_annotation => r
  | CLOSEFIX rlist => CLOSEFIX (map f rlist)
  | FNAPP => r
  | VSCONS => r
  | LISTRULE _ => r

fun fupdate_rule_by_term t f r = let
  fun over_rr (rr:rule_record) = if #term_name rr = t then f rr else rr
in
  map_rrfn_rule over_rr r
end

fun fupdate_rule_by_termtok {term_name, tok} f r = let
  fun over_rr (rr:rule_record) =
    if #term_name rr = term_name andalso
      List.exists (fn e => e = TOK tok) (rule_elements (#elements rr)) then
      f rr
    else
      rr
in
  map_rrfn_rule over_rr r
end

fun fupdate_rulelist f rules = map (fn (p,r) => (p, f r)) rules
fun fupdate_prulelist f rules = map f rules


fun binder_to_string (G:grammar) b =
  case b of
    LAMBDA => #lambda (#specials G)
  | BinderString s => s

fun binders (G: grammar) = let
  fun binders0 [] acc = acc
    | binders0 ((_, x)::xs) acc = let
      in
        case x of
          PREFIX (BINDER sl) => binders0 xs (map (binder_to_string G) sl @ acc)
        | _ => binders0 xs acc
      end
in
  binders0 (#rules G) []
end

fun resquan_op (G: grammar) = #res_quanop (specials G)

fun update_assoc (item as (k,v)) alist =
  case alist of
    [] => [item]
  | (first as (k1,v1))::rest => if k = k1 then item::rest
                                else first::update_assoc item rest

fun associate_restriction G (b, s) =
  fupdate_specials (fupdate_restr_binders (update_assoc (b, s))) G

fun is_binder (G:grammar) = let
  val bs = binders G
  fun member x [] = false
    | member x (y::ys) = x = y orelse member x ys
in
  fn s => member s bs
end

datatype stack_terminal =
  STD_HOL_TOK of string | BOS | EOS | Id  | TypeColon | TypeTok | EndBinding |
  VS_cons | ResquanOpTok

fun STtoString (G:grammar) x =
  case x of
    STD_HOL_TOK s => s
  | BOS => "<beginning of input>"
  | EOS => "<end of string>"
  | VS_cons => "<gap between varstructs>"
  | Id => "<identifier>"
  | TypeColon => #type_intro (#specials G)
  | TypeTok => "<type>"
  | EndBinding => #endbinding (#specials G) ^ " (end binding)"
  | ResquanOpTok => #res_quanop (#specials G)^" (res quan operator)"

val stdhol : grammar =
  {rules = [(SOME 0, PREFIX (BINDER [LAMBDA])),
            (SOME 4, INFIX RESQUAN_OP),
            (SOME 5, VSCONS),
            (SOME 6,
             INFIX (STD_infix([{term_name = recupd_special,
                                elements = [RE (TOK ":=")],
                                preferred = false,
                                block_style = (AroundEachPhrase,
                                                (PP.CONSISTENT, 0)),
                                 paren_style = OnlyIfNecessary},
                               {term_name = recwith_special,
                                elements = [RE (TOK "with")],
                                preferred = false,
                                block_style = (AroundEachPhrase,
                                                (PP.CONSISTENT, 0)),
                                 paren_style = OnlyIfNecessary}], NONASSOC))),
            (SOME 1000, SUFFIX TYPE_annotation),
            (SOME 2000, FNAPP),
            (SOME 2500,
             INFIX (STD_infix ([{term_name = recsel_special,
                                 elements = [RE (TOK ".")],
                                 preferred = false,
                                 block_style = (AroundEachPhrase,
                                                (PP.CONSISTENT, 0)),
                                 paren_style = OnlyIfNecessary}], LEFT))),
            (NONE,
             CLOSEFIX [{term_name = bracket_special,
                        elements = [RE (TOK "("), RE TM, RE (TOK ")")],
                        preferred = false,
                        (* these two elements here will not actually
                         ever be looked at by the printer *)
                        block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                        paren_style = Always}]),
            (NONE,
             LISTRULE [{separator = ";", leftdelim = "<[", rightdelim = "]>",
                        cons = reccons_special, nilstr = recnil_special}])],
   specials = {lambda = "\\", type_intro = ":", endbinding = ".",
               restr_binders = [], res_quanop = "::"},
   numeral_info = [],
   overload_info = []
   }

local
  open stmonad
  infix >>
  fun add x acc = (x::acc, ())
  fun specials_from_elm [] = ok
    | specials_from_elm ((TOK x)::xs) = add x >> specials_from_elm xs
    | specials_from_elm (TM::xs) = specials_from_elm xs
  val mmap = (fn f => fn args => mmap f args >> ok)
  fun rule_specials G r = let
    val rule_specials = rule_specials G
  in
    case r of
      PREFIX(STD_prefix rules) =>
        mmap (specials_from_elm o rule_elements o #elements) rules
    | PREFIX (BINDER b) =>
        mmap add (map (binder_to_string G) b)
    | SUFFIX(STD_suffix rules) =>
        mmap (specials_from_elm o rule_elements o #elements) rules
    | SUFFIX TYPE_annotation => add (#type_intro (#specials G))
    | INFIX(STD_infix (rules, _)) =>
        mmap (specials_from_elm o rule_elements o #elements) rules
    | INFIX RESQUAN_OP => ok
    | CLOSEFIX rules =>
        mmap (specials_from_elm o rule_elements o #elements) rules
    | LISTRULE rlist => let
        fun process r =
          add (#separator r) >> add (#leftdelim r) >> add (#rightdelim r)
      in
        mmap process rlist
      end
    | FNAPP => ok
    | VSCONS => ok
  end
in
  fun grammar_tokens G = let
    fun gs (G:grammar) = mmap (rule_specials G o #2) (#rules G)
    val (all_specials, ()) = gs G []
  in
    Lib.mk_set all_specials
  end
  fun rule_tokens G r = Lib.mk_set (#1 (rule_specials G r []))
end

(* turn a rule element list into a list of std_hol_toks *)
val rel_list_to_toklist =
  List.mapPartial (fn TOK s => SOME (STD_HOL_TOK s) | _ => NONE)

(* right hand elements of suffix and closefix rules *)
fun find_suffix_rhses (G : grammar) = let
  fun select (SUFFIX TYPE_annotation) = [[TypeTok]]
    | select (SUFFIX (STD_suffix rules)) = let
      in
        map (rel_list_to_toklist o rule_elements o #elements) rules
        end
    | select (CLOSEFIX rules) =
        map (rel_list_to_toklist o rule_elements o #elements) rules
    | select (LISTRULE rlist) =
        map (fn r => [STD_HOL_TOK (#rightdelim r)]) rlist
    | select _ = []
  val suffix_rules = List.concat (map (select o #2) (#rules G))
in
  Id :: map List.last suffix_rules
end

fun find_prefix_lhses (G : grammar) = let
  fun select x = let
  in
    case x of
      PREFIX (STD_prefix rules) =>
        map (rel_list_to_toklist o rule_elements o #elements) rules
    | PREFIX (BINDER sl) =>
        map (fn b => [STD_HOL_TOK (binder_to_string G b)]) sl
    | CLOSEFIX rules =>
        map (rel_list_to_toklist o rule_elements o #elements) rules
    | (LISTRULE rlist) =>
        map (fn r => [STD_HOL_TOK (#leftdelim r)]) rlist
    | _ => []
  end
  val prefix_rules = List.concat (map (select o #2) (#rules G))
in
  Id :: map hd prefix_rules
end

fun compatible_listrule (G:grammar) arg = let
  val {separator, leftdelim, rightdelim} = arg
  fun recurse rules =
    case rules of
      [] => NONE
    | ((_, rule)::rules) => let
      in
        case rule of
          LISTRULE rlist => let
            fun check [] = NONE
              | check (r::rs) = let
                  val rule_sep = #separator r
                  val rule_left = #leftdelim r
                  val rule_right = #rightdelim r
                in
                  if rule_sep = separator andalso rule_left = leftdelim andalso
                    rule_right = rightdelim then
                    SOME {cons = #cons r, nilstr = #nilstr r}
                  else
                    check rs
                end
            val result = check rlist
          in
            if isSome result then result else  recurse rules
          end
        | _ => recurse rules
      end
in
  recurse (#rules G)
end

fun grammar_rules (G:grammar) = map #2 (#rules G)
fun rules (G : grammar) = (#rules G)

fun aug_compare (NONE, NONE) = EQUAL
  | aug_compare (_, NONE) = LESS
  | aug_compare (NONE, _) = GREATER
  | aug_compare (SOME n, SOME m) = Int.compare(n,m)

fun priv_a2string a =
  case a of
    LEFT => "LEFT"
  | RIGHT => "RIGHT"
  | NONASSOC => "NONASSOC"

fun merge_rules (r1, r2) =
  case (r1, r2) of
    (SUFFIX (STD_suffix sl1), SUFFIX (STD_suffix sl2)) =>
      SUFFIX (STD_suffix (sl1 @ sl2))
  | (SUFFIX TYPE_annotation, SUFFIX TYPE_annotation) => r1
  | (PREFIX (STD_prefix pl1), PREFIX (STD_prefix pl2)) =>
      PREFIX (STD_prefix (pl1 @ pl2))
  | (PREFIX (BINDER b1), PREFIX (BINDER b2)) => PREFIX (BINDER (b1 @ b2))
  | (INFIX(STD_infix (i1, a1)), INFIX(STD_infix(i2, a2))) =>
      if a1 <> a2 then
        raise GrammarError
          ("Attempt to have differently associated infixes ("^
           priv_a2string a1^" and "^priv_a2string a2^") at same level")
      else
        INFIX(STD_infix(Lib.union i1 i2, a1))
  | (INFIX RESQUAN_OP, INFIX RESQUAN_OP) => INFIX(RESQUAN_OP)
  | (CLOSEFIX c1, CLOSEFIX c2) => CLOSEFIX (c1 @ c2)
  | (FNAPP, FNAPP) => FNAPP
  | (LISTRULE lr1, LISTRULE lr2) => LISTRULE (lr1 @ lr2)
  | _ => raise GrammarError "Attempt to have different forms at same level"


fun resolve_same_precs [] = []
  | resolve_same_precs [x] = [x]
  | resolve_same_precs ((p1, r1)::(rules1 as (p2, r2)::rules2)) = let
    in
      if p1 <> p2 orelse not (isSome p1) then
        (p1, r1)::(resolve_same_precs rules1)
      else
        (p1, merge_rules (r1, r2)) :: resolve_same_precs rules2
    end

infix Gmerge
(* only merges rules, keeps rest as in g1 *)
fun ((g1:grammar) Gmerge (g2:(int option * grammar_rule) list)) = let
  val g0_rules =
    Listsort.sort (fn (e1,e2) => aug_compare(#1 e1, #1 e2))
    (#rules g1 @ g2)
  val g_rules =  resolve_same_precs g0_rules
in
  fupdate_rules (fn _ => g_rules) g1
end

fun null_rule r =
  case r of
    SUFFIX (STD_suffix slist) => null slist
  | PREFIX (STD_prefix slist) => null slist
  | PREFIX (BINDER slist) => null slist
  | INFIX (STD_infix(slist, _)) => null slist
  | CLOSEFIX slist => null slist
  | _ => false

fun map_rules f G = let
  fun recurse r =
    case r of
      [] => []
    | ((prec, rule)::rules) => let
        val newrule = f rule
        val rest = recurse rules
      in
        if null_rule newrule then rest else (prec, newrule)::rest
      end
in
  fupdate_rules recurse G
end



fun remove_form s rule = let
  fun rr_ok (r:rule_record) = #term_name r <> s
  fun stringbinder LAMBDA = false | stringbinder (BinderString s0) = s0 = s
in
  case rule of
    SUFFIX (STD_suffix slist) => SUFFIX (STD_suffix (List.filter rr_ok slist))
  | INFIX (STD_infix(slist, assoc)) =>
      INFIX(STD_infix (List.filter rr_ok slist, assoc))
  | PREFIX (STD_prefix slist) => PREFIX (STD_prefix (List.filter rr_ok slist))
  | PREFIX (BINDER slist) =>
      PREFIX (BINDER (List.filter (not o stringbinder) slist))
  | CLOSEFIX slist => CLOSEFIX (List.filter rr_ok slist)
  | _ => rule
end


fun remove_tok {term_name, tok} r = let
  fun rels_safe rels = not (List.exists (fn e => e = TOK tok) rels)
  fun rr_safe {term_name = s, elements,...} =
    s <> term_name orelse rels_safe (rule_elements elements)
in
  case r of
    SUFFIX (STD_suffix slist) =>
      SUFFIX (STD_suffix (List.filter rr_safe slist))
  | INFIX(STD_infix (slist, assoc)) =>
      INFIX (STD_infix (List.filter rr_safe slist, assoc))
  | PREFIX (STD_prefix slist) =>
      PREFIX (STD_prefix (List.filter rr_safe slist))
  | CLOSEFIX slist => CLOSEFIX (List.filter rr_safe slist)
  | LISTRULE rlist => let
      fun lrule_ok r =
        (#cons r <> term_name andalso #nilstr r <> term_name)  orelse
        (#leftdelim r <> tok andalso #rightdelim r <> tok andalso
         #separator r <> tok)
    in
      LISTRULE (List.filter lrule_ok rlist)
    end
  | _ => r
end

fun remove_standard_form G s = map_rules (remove_form s) G
fun remove_form_with_tok G r = map_rules (remove_tok r) G


datatype rule_fixity =
  Infix of associativity * int | Closefix | Suffix of int | TruePrefix of int
fun rule_fixityToString f =
  case f of
    Infix(a,i) => "term_grammar.Infix("^assocToString a^", "^Int.toString i^")"
  | Closefix => "term_grammar.Closefix"
  | Suffix p => "term_grammar.Suffix "^Int.toString p
  | TruePrefix p => "term_grammar.TruePrefix "^Int.toString p


fun clear_prefs_for s =
  fupdate_rules
  (fupdate_rulelist (fupdate_rule_by_term s (update_rr_pref false)))


fun add_rule G0 {term_name = s, fixity = f, pp_elements,
                 paren_style, block_style} = let
  val _ =  pp_elements_ok pp_elements orelse
                 raise GrammarError "token list no good"
  val G1 = clear_prefs_for s G0
  val rr = {term_name = s, elements = pp_elements, preferred = true,
            paren_style = paren_style, block_style = block_style}
  val new_rule =
    case f of
      Infix (a,p) => (SOME p, INFIX(STD_infix([rr], a)))
    | Suffix p => (SOME p, SUFFIX (STD_suffix [rr]))
    | TruePrefix p => (SOME p, PREFIX (STD_prefix [rr]))
    | Closefix => (NONE, CLOSEFIX [rr])
in
  G1 Gmerge [new_rule]
end

fun add_grule G0 r = G0 Gmerge [r]

fun add_binder G0 (s, prec) =
  G0 Gmerge [(SOME prec, PREFIX (BINDER [BinderString s]))]

fun add_listform G lrule = G Gmerge [(NONE, LISTRULE [lrule])]

fun prefer_form_with_tok (G0:grammar) (r as {term_name,tok}) = let
  val G1 = clear_prefs_for term_name G0
in
  fupdate_rules
  (fupdate_rulelist
   (fupdate_rule_by_termtok r (update_rr_pref true))) G1
end

fun set_associativity_at_level G (p, ass) =
  fupdate_rules
  (fupdate_prulelist
   (fn (p', r) =>
    if isSome p' andalso p = valOf p' then
      (p', (case r of
             INFIX(STD_infix(els, _)) => INFIX (STD_infix(els, ass))
           | _ => r))
    else
      (p', r))) G

fun find_partial f [] = NONE
  | find_partial f (x::xs) = let
    in
      case f x of
        NONE => find_partial f xs
      | y => y
    end

fun get_precedence ({rules,...}:grammar) s = let
  fun check_rule (p, r) = let
    fun elmem s [] = false
      | elmem s ({elements, ...}::xs) =
      Lib.mem (TOK s) (rule_elements elements) orelse elmem s xs
  in
    case r of
      INFIX(STD_infix (elms, assoc)) =>
        if elmem s elms then SOME(Infix(assoc, valOf p))
        else NONE
    | PREFIX(STD_prefix elms) =>
          if elmem s elms then SOME (TruePrefix (valOf p))
          else NONE
    | SUFFIX (STD_suffix elms) => if elmem s elms then SOME (Suffix (valOf p))
                                  else NONE
    | CLOSEFIX elms => if elmem s elms then SOME Closefix else NONE
    | _ => NONE
  end
in
  find_partial check_rule rules
end

fun update_assoc (k,v) alist = let
    val (_, newlist) = Lib.pluck (fn (k', _) => k' = k) alist
  in
    (k,v)::newlist
  end handle _ => (k,v)::alist


fun check c =
  if Char.isAlpha c then Char.toLower c
  else raise GrammarError "Numeric type suffixes must be letters"

fun add_numeral_form G (c, stropt) =
  fupdate_numinfo (update_assoc (check c, stropt)) G

fun give_num_priority G c = let
  val realc = check c
  fun update_fn alist = let
    val (oldval, rest) = Lib.pluck (fn (k,_) => k = realc) alist
  in
    oldval::rest
  end handle _ => raise GrammarError "No such numeral type in grammar"
in
  fupdate_numinfo update_fn G
end

fun remove_numeral_form G c =
  fupdate_numinfo (List.filter (fn (k,v) => k <> (check c))) G
