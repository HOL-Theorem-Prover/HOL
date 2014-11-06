structure term_grammar :> term_grammar =
struct

open HOLgrammars GrammarSpecials Lib Feedback

  type ppstream = Portable.ppstream

type term = Term.term

type nthy_rec = {Name : string, Thy : string}

  type block_info = PP.break_style * int
  datatype rule_element = TOK of string | TM
  fun RE_compare (TOK s1, TOK s2) = String.compare(s1,s2)
    | RE_compare (TOK _, TM) = LESS
    | RE_compare (TM, TOK _) = GREATER
    | RE_compare (TM, TM) = EQUAL
  datatype pp_element =
    PPBlock of pp_element list * block_info |
    EndInitialBlock of block_info | BeginFinalBlock of block_info |
    HardSpace of int | BreakSpace of (int * int) |
    RE of rule_element | LastTM | FirstTM
  (* these last two only used internally *)

    datatype PhraseBlockStyle =
      AroundSameName | AroundSamePrec | AroundEachPhrase | NoPhrasing
    datatype ParenStyle =
      Always | OnlyIfNecessary | ParoundName | ParoundPrec | NotEvenIfRand

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
                    timestamp : int,
                    block_style : PhraseBlockStyle * block_info,
                    paren_style : ParenStyle}

datatype binder = LAMBDA
                | BinderString of {tok : string, term_name : string,
                                   timestamp : int}

datatype prefix_rule = STD_prefix of rule_record list | BINDER of binder list
datatype suffix_rule = STD_suffix of rule_record list | TYPE_annotation
datatype infix_rule =
         STD_infix of rule_record list * associativity
       | RESQUAN_OP
       | VSCONS
       | FNAPP of rule_record list

type listspec =
  {separator : pp_element list, leftdelim : pp_element list,
   rightdelim : pp_element list, cons : string, nilstr : string,
   block_info : block_info}

datatype grammar_rule =
         PREFIX of prefix_rule
       | SUFFIX of suffix_rule
       | INFIX of infix_rule
       | CLOSEFIX of rule_record list
       | LISTRULE of listspec list

datatype rule_fixity =
  Infix of associativity * int | Closefix | Suffix of int | Prefix of int

datatype user_delta =
         GRULE of {term_name : string,
                   fixity : rule_fixity,
                   pp_elements: pp_element list,
                   paren_style : ParenStyle,
                   block_style : PhraseBlockStyle * block_info}
       | LRULE of listspec
       | BRULE of {tok : string, term_name : string}

fun pptoks ppels = List.mapPartial (fn TOK s => SOME s | _ => NONE)
                                   (rule_elements ppels)
fun userdelta_toks ud =
    case ud of
      GRULE {pp_elements, ...} => pptoks pp_elements
    | BRULE {tok,...} => [tok]
    | LRULE {leftdelim, separator, rightdelim, ...} =>
      pptoks leftdelim @ pptoks separator @ pptoks rightdelim

fun userdelta_name ud =
    case ud of
      GRULE {term_name, ...} => term_name
    | BRULE {term_name, ...} => term_name
    | LRULE {cons, ...} => cons


type overload_info = Overload.overload_info

type 'a printer_info =
  (term * string * 'a term_pp_types.userprinter) Net.net * string Binaryset.set
type special_info = {type_intro : string,
                     lambda : string list,
                     endbinding : string,
                     restr_binders : (string option * string) list,
                     res_quanop : string}


datatype grammar = GCONS of
  {rules : (int option * grammar_rule) list,
   specials : special_info,
   numeral_info : (char * string option) list,
   overload_info : overload_info,
   user_printers : (type_grammar.grammar * grammar) printer_info,
   absyn_postprocessors : (string * (Absyn.absyn -> Absyn.absyn)) list
   }

type userprinter = (type_grammar.grammar * grammar) term_pp_types.userprinter

fun specials (GCONS G) = #specials G
fun numeral_info (GCONS G) = #numeral_info G
fun overload_info (GCONS G) = #overload_info G
fun known_constants (GCONS G) = Overload.known_constants (#overload_info G)
fun grammar_rules (GCONS G) = map #2 (#rules G)
fun rules (GCONS G) = (#rules G)
fun absyn_postprocessors (GCONS g) = #absyn_postprocessors g

(* fupdates *)
open FunctionalRecordUpdate
infix &
fun makeUpdateG z = makeUpdate A A A A A A $$ z (* 6 A's - 6 fields *)
fun update_G z = let
  fun p2r (rules & specials & numeral_info & overload_info & user_printers &
           absyn_postprocessors) =
        {rules = rules, specials = specials, numeral_info = numeral_info,
         overload_info = overload_info, user_printers = user_printers,
         absyn_postprocessors = absyn_postprocessors}
    fun r2p  {rules, specials, numeral_info, overload_info, user_printers,
              absyn_postprocessors} =
        (rules & specials & numeral_info & overload_info & user_printers &
         absyn_postprocessors)
  in
    makeUpdateG (p2r, p2r, r2p)
  end z


fun fupdate_rules f (GCONS g) =
    GCONS (update_G g (U #rules (f (#rules g))) $$)
fun fupdate_specials f (GCONS g) =
  GCONS (update_G g (U #specials (f (#specials g))) $$)
fun fupdate_numinfo f (GCONS g) =
  GCONS (update_G g (U #numeral_info (f (#numeral_info g))) $$)

fun mfupdate_overload_info f (GCONS g) = let
  val (new_oinfo,result) = f (#overload_info g)
in
  (GCONS (update_G g (U #overload_info new_oinfo) $$), result)
end
fun fupdate_overload_info f g =
  #1 (mfupdate_overload_info (fn oi => (f oi, ())) g)

val strip_overload_info = fupdate_overload_info (fn _ => Overload.null_oinfo)

fun mfupdate_user_printers f (GCONS g) = let
  val (new_uprinters, result) = f (#user_printers g)
in
  (GCONS (update_G g (U #user_printers new_uprinters) $$), result)
end

fun grammar_name G tm = let
  val oinfo = overload_info G
in
  if Term.is_const tm then
    Overload.overloading_of_term oinfo tm
  else if Term.is_var tm then let
      val (vnm, _) = Term.dest_var tm
    in
      Option.map #fake (GrammarSpecials.dest_fakeconst_name vnm)
    end
  else NONE
end


(* invariant of user_printers is that there is only ever one value with a
   given name in the mapping from terms to print functions *)
fun fupdate_user_printers f g =
  #1 (mfupdate_user_printers (fn ups => (f ups, ())) g)

fun user_printers (GCONS g) = #1 (#user_printers g)

fun remove_user_printer k (GCONS g) = let
  val (net, keyset) = #user_printers g
in
  if Binaryset.member(keyset,k) then let
      fun foldthis (t,nm,f) (olddata,newnet) =
          if nm = k then (SOME (t,f), newnet)
          else (olddata, Net.insert(t,(t,nm,f)) newnet)
      val (data, newnet) = Net.itnet foldthis net (NONE, Net.empty)
      val newkeys = Binaryset.delete(keyset, k)
    in
      (GCONS (update_G g (U #user_printers (newnet,newkeys)) $$),
       data)
    end
  else (GCONS g, NONE)
end

fun add_user_printer (k,pat,v) g = let
  val (g', _) = remove_user_printer k g
  fun upd (net,keys) = (Net.insert(pat, (pat,k,v)) net, Binaryset.add(keys, k))
in
  fupdate_user_printers upd g'
end

fun update_alist (k,v) [] = [(k,v)]
  | update_alist (k,v) ((kv as (k',_))::rest) =
    if k = k' then (k,v) :: rest
    else kv :: update_alist (k,v) rest

fun new_absyn_postprocessor (k,f) (GCONS g) = let
  val old = #absyn_postprocessors g
in
  GCONS (update_G g (U #absyn_postprocessors (update_alist (k,f) old)) $$)
end

fun remove_absyn_postprocessor k (GCONS g) = let
  val old = #absyn_postprocessors g
in
  case total (pluck (equal k o #1)) old of
    NONE => (GCONS g, NONE)
  | SOME ((_,f), rest) =>
    (GCONS (update_G g (U #absyn_postprocessors rest) $$), SOME f)
end


fun update_restr_binders rb
  {lambda, endbinding, type_intro, restr_binders, res_quanop} =
  {lambda = lambda, endbinding = endbinding, type_intro = type_intro,
         restr_binders = rb, res_quanop = res_quanop}

fun fupdate_restr_binders f
  {lambda, endbinding, type_intro, restr_binders, res_quanop} =
  {lambda = lambda, endbinding = endbinding, type_intro = type_intro,
   restr_binders = f restr_binders, res_quanop = res_quanop}

fun map_rrfn_rule f g r =
  case r of
    PREFIX (STD_prefix rlist) => PREFIX (STD_prefix (map f rlist))
  | PREFIX (BINDER bslist) => PREFIX (BINDER (map g bslist))

  | INFIX (STD_infix (rlist, a)) => INFIX (STD_infix (map f rlist, a))
  | INFIX RESQUAN_OP => r
  | INFIX (FNAPP rlist) => INFIX (FNAPP (map f rlist))
  | INFIX VSCONS => r

  | SUFFIX (STD_suffix rlist) => SUFFIX (STD_suffix (map f rlist))
  | SUFFIX TYPE_annotation => r

  | CLOSEFIX rlist => CLOSEFIX (map f rlist)
  | LISTRULE _ => r

fun fupdate_rule_by_term t f g r = let
  fun over_rr (rr:rule_record) = if #term_name rr = t then f rr else rr
  fun over_br LAMBDA = LAMBDA
    | over_br (b as BinderString {term_name,...}) =
      if term_name = t then g b else b
in
  map_rrfn_rule over_rr over_br r
end

fun fupdate_rule_by_termtok {term_name, tok} f g r = let
  fun over_rr (rr:rule_record) =
    if #term_name rr = term_name andalso
      List.exists (fn e => e = TOK tok) (rule_elements (#elements rr)) then
      f rr
    else
      rr
  fun over_br LAMBDA = LAMBDA
    | over_br (b as BinderString {term_name = tnm, tok = tk, ...}) =
      if term_name = tnm andalso tk = tok then g b else b
in
  map_rrfn_rule over_rr over_br r
end

fun fupdate_rule_by_termtoklist {term_name,toklist} f g r = let
  fun toks rr = pptoks (#elements rr)
  fun over_rr (rr:rule_record) =
      if #term_name rr = term_name andalso toks rr = toklist then
        f rr
      else
        rr
  fun over_br LAMBDA = LAMBDA
    | over_br (b as BinderString {term_name = tnm, tok, ...}) =
      if term_name = tnm andalso [tok] = toklist then g b else b
in
  map_rrfn_rule over_rr over_br r
end

fun fupdate_rulelist f rules = map (fn (p,r) => (p, f r)) rules
fun fupdate_prulelist f rules = map f rules

fun update_b_tstamp _ LAMBDA = LAMBDA
  | update_b_tstamp t (BinderString {tok,term_name,timestamp}) =
    BinderString {tok = tok, term_name =term_name, timestamp = t}

fun update_rr_tstamp t {term_name, elements, paren_style,
                        block_style, timestamp} =
    {term_name = term_name, elements = elements, paren_style = paren_style,
     block_style = block_style, timestamp = t}


fun binder_to_string (G:grammar) b =
  case b of
    LAMBDA => hd (#lambda (specials G))
  | BinderString {term_name,...} => term_name

(* the concrete tokens of the grammar corresponding to bind syntax. *)
fun binders (G: grammar) = let
  fun b2str (LAMBDA, acc) = #lambda (specials G) @ acc
    | b2str (BinderString r, acc) = (#tok r)::acc
  fun binders0 [] acc = acc
    | binders0 ((_, x)::xs) acc = let
      in
        case x of
          PREFIX (BINDER sl) => binders0 xs (List.foldl b2str acc sl)
        | _ => binders0 xs acc
      end
in
  binders0 (rules G) []
end

fun resquan_op (G: grammar) = #res_quanop (specials G)

fun update_assoc (item as (k,v)) alist =
  case alist of
    [] => [item]
  | (first as (k1,v1))::rest => if k = k1 then item::rest
                                else first::update_assoc item rest

fun associate_restriction G {binder = b, resbinder = s} =
  fupdate_specials (fupdate_restr_binders (update_assoc (b, s))) G

fun is_binder G = let val bs = binders G in fn s => Lib.mem s bs end

datatype stack_terminal =
  STD_HOL_TOK of string | BOS | EOS | Id  | TypeColon | TypeTok | EndBinding |
  VS_cons | ResquanOpTok

fun STi st =
    case st of
      STD_HOL_TOK _ => 0
    | BOS => 1
    | EOS => 2
    | Id => 3
    | TypeColon => 4
    | TypeTok => 5
    | EndBinding => 6
    | VS_cons => 7
    | ResquanOpTok => 8
fun ST_compare (p as (st1,st2)) =
    case p of
      (STD_HOL_TOK s1, STD_HOL_TOK s2) => String.compare(s1,s2)
    | _ => Lib.measure_cmp STi p

fun STtoString (G:grammar) x =
  case x of
    STD_HOL_TOK s => s
  | BOS => "<beginning of input>"
  | EOS => "<end of input>"
  | VS_cons => "<gap between varstructs>"
  | Id => "<identifier>"
  | TypeColon => #type_intro (specials G)
  | TypeTok => "<type>"
  | EndBinding => #endbinding (specials G) ^ " (end binding)"
  | ResquanOpTok => #res_quanop (specials G)^" (res quan operator)"

(* gives the "wrong" lexicographic order, but is more likely to
   resolve differences with one comparison because types/terms with
   the same name are rare, but it's quite reasonable for many
   types/terms to share the same theory *)
fun nthy_compare ({Name = n1, Thy = thy1}, {Name = n2, Thy = thy2}) =
  case String.compare(n1, n2) of
    EQUAL => String.compare(thy1, thy2)
  | x => x


val stdhol : grammar =
  GCONS
  {rules = [(SOME 0, PREFIX (BINDER [LAMBDA])),
            (SOME 4, INFIX RESQUAN_OP),
            (SOME 5, INFIX VSCONS),
            (SOME 460,
             INFIX (STD_infix([{term_name = recwith_special,
                                elements = [RE (TOK "with")],
                                timestamp = 0,
                                block_style = (AroundEachPhrase,
                                                (PP.CONSISTENT, 0)),
                                paren_style = OnlyIfNecessary},
                               {term_name = recupd_special,
                                elements = [RE (TOK ":=")],
                                timestamp = 0,
                                block_style = (AroundEachPhrase,
                                                (PP.CONSISTENT, 0)),
                                paren_style = OnlyIfNecessary},
                               {term_name = recfupd_special,
                                elements = [RE (TOK "updated_by")],
                                timestamp = 0,
                                block_style = (AroundEachPhrase,
                                                (PP.CONSISTENT, 0)),
                                paren_style = OnlyIfNecessary}], RIGHT))),
            (SOME 899, SUFFIX TYPE_annotation),
            (SOME 2000, INFIX (FNAPP [])),
            (SOME 2500,
             INFIX (STD_infix ([{term_name = recsel_special,
                                 elements = [RE (TOK ".")],
                                 timestamp = 0,
                                 block_style = (AroundEachPhrase,
                                                (PP.CONSISTENT, 0)),
                                 paren_style = OnlyIfNecessary}], LEFT))),
            (NONE,
             CLOSEFIX [{term_name = bracket_special,
                        elements = [RE (TOK "("), RE TM, RE (TOK ")")],
                        timestamp = 0,
                        (* these two elements here will not actually
                         ever be looked at by the printer *)
                        block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                        paren_style = Always}]),
            (NONE,
             LISTRULE [{separator = [RE (TOK ";"), BreakSpace(1,0)],
                        leftdelim = [RE (TOK "<|")],
                        rightdelim = [RE (TOK "|>")],
                        block_info = (PP.INCONSISTENT, 0),
                        cons = reccons_special, nilstr = recnil_special}])],
   specials = {lambda = ["\\"], type_intro = ":", endbinding = ".",
               restr_binders = [], res_quanop = "::"},
   numeral_info = [],
   overload_info = Overload.null_oinfo,
   user_printers = (Net.empty, Binaryset.empty String.compare),
   absyn_postprocessors = []
   }

fun first_tok [] = raise Fail "Shouldn't happen parse_term 133"
  | first_tok (RE (TOK s)::_) = s
  | first_tok (_ :: t) = first_tok t

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
    | PREFIX (BINDER b) => ok
    | SUFFIX(STD_suffix rules) =>
        mmap (specials_from_elm o rule_elements o #elements) rules
    | SUFFIX TYPE_annotation => add (#type_intro (specials G))
    | INFIX(STD_infix (rules, _)) =>
        mmap (specials_from_elm o rule_elements o #elements) rules
    | INFIX RESQUAN_OP => ok
    | INFIX (FNAPP rlst) =>
        mmap (specials_from_elm o rule_elements o #elements) rlst
    | INFIX VSCONS => ok
    | CLOSEFIX rules =>
        mmap (specials_from_elm o rule_elements o #elements) rules
    | LISTRULE rlist => let
        fun process (r:listspec) =
          add (first_tok (#separator r)) >>
          add (first_tok (#leftdelim r)) >>
          add (first_tok (#rightdelim r))
      in
        mmap process rlist
      end
  end
in
  fun grammar_tokens G = let
    fun gs (G:grammar) = mmap (rule_specials G o #2) (rules G) >>
                         mmap add (binders G)
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
        map (fn r => [STD_HOL_TOK (first_tok (#rightdelim r))]) rlist
    | select _ = []
  val suffix_rules = List.concat (map (select o #2) (rules G))
in
  Id :: map List.last suffix_rules
end

fun find_prefix_lhses (G : grammar) = let
  fun select x = let
  in
    case x of
      PREFIX (STD_prefix rules) =>
        map (rel_list_to_toklist o rule_elements o #elements) rules
    | CLOSEFIX rules =>
        map (rel_list_to_toklist o rule_elements o #elements) rules
    | (LISTRULE rlist) =>
        map (fn r => [STD_HOL_TOK (first_tok (#leftdelim r))]) rlist
    | _ => []
  end
  val prefix_rules = List.concat (map (select o #2) (rules G))
in
  Id :: map STD_HOL_TOK (binders G) @ map hd prefix_rules
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
              | check ((r:listspec)::rs) = let
                  val rule_sep = first_tok (#separator r)
                  val rule_left = first_tok (#leftdelim r)
                  val rule_right = first_tok (#rightdelim r)
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
  recurse (rules G)
end


fun aug_compare (NONE, NONE) = EQUAL
  | aug_compare (_, NONE) = LESS
  | aug_compare (NONE, _) = GREATER
  | aug_compare (SOME n, SOME m) = Int.compare(n,m)

fun priv_a2string a =
  case a of
    LEFT => "LEFT"
  | RIGHT => "RIGHT"
  | NONASSOC => "NONASSOC"

fun rr_eq (rr1: rule_record) (rr2 : rule_record) =
    (* ignore timestamp field *)
    #term_name   rr1 = #term_name   rr2 andalso
    #elements    rr1 = #elements    rr2 andalso
    #block_style rr1 = #block_style rr2 andalso
    #paren_style rr1 = #paren_style rr2
val rrunion = Lib.op_union rr_eq

fun tokb_eq b1 b2 =
    case (b1,b2) of
      (LAMBDA, LAMBDA) => true
    | (BinderString{tok=tk1, term_name = nm1,...},
       BinderString{tok=tk2, term_name = nm2,...}) => tk1 = tk2 andalso
                                                      nm1 = nm2
    | _ => false
val bunion = Lib.op_union tokb_eq

fun merge_rules (r1, r2) =
  case (r1, r2) of
    (SUFFIX (STD_suffix sl1), SUFFIX (STD_suffix sl2)) =>
      SUFFIX (STD_suffix (rrunion sl1 sl2))
  | (SUFFIX TYPE_annotation, SUFFIX TYPE_annotation) => r1
  | (PREFIX (STD_prefix pl1), PREFIX (STD_prefix pl2)) =>
      PREFIX (STD_prefix (rrunion pl1 pl2))
  | (PREFIX (BINDER b1), PREFIX (BINDER b2)) =>
      PREFIX (BINDER (bunion b1 b2))
  | (INFIX VSCONS, INFIX VSCONS) => INFIX VSCONS
  | (INFIX(STD_infix (i1, a1)), INFIX(STD_infix(i2, a2))) =>
      if a1 <> a2 then
        raise GrammarError
          ("Attempt to have differently associated infixes ("^
           priv_a2string a1^" and "^priv_a2string a2^") at same level")
      else
        INFIX(STD_infix(rrunion i1 i2, a1))
  | (INFIX RESQUAN_OP, INFIX RESQUAN_OP) => INFIX(RESQUAN_OP)
  | (INFIX (FNAPP rl1), INFIX (FNAPP rl2)) => INFIX (FNAPP (rrunion rl1 rl2))
  | (INFIX (STD_infix(i1, a1)), INFIX (FNAPP rl1)) =>
      if a1 <> LEFT then
        raise GrammarError
                ("Attempting to merge function application with non-left" ^
                 " associated infix")
      else INFIX (FNAPP (rrunion i1 rl1))
  | (INFIX (FNAPP _), INFIX (STD_infix _)) => merge_rules (r2, r1)
  | (CLOSEFIX c1, CLOSEFIX c2) => CLOSEFIX (rrunion c1 c2)
  | (LISTRULE lr1, LISTRULE lr2) => LISTRULE (Lib.union lr1 lr2)
  | _ => raise GrammarError "Attempt to have different forms at same level"

fun optmerge r NONE = SOME r
  | optmerge r1 (SOME r2) = SOME (merge_rules (r1, r2))

(* the listrule and closefix rules don't have precedences and sit at the
   end of the list.  When merging grammars, we will have a list of possibly
   intermingled closefix and listrule rules to look at, we want to produce
   just one closefix and one listrule rule for the final grammar *)

(* This allows for reducing more than just two closefix and listrules, but
   when merging grammars with only one each, this shouldn't eventuate *)
fun resolve_nullprecs listrule closefix rules =
  case rules of
    [] => let
    in
      case (listrule, closefix) of
        (NONE, NONE) => [] (* should never really happen *)
      | (SOME lr, NONE) => [(NONE, lr)]
      | (NONE, SOME cf) => [(NONE, cf)]
      | (SOME lr, SOME cf) => [(NONE, lr), (NONE, cf)]
    end
  | (_, r as LISTRULE _)::xs =>
    resolve_nullprecs (optmerge r listrule) closefix xs
  | (_, r as CLOSEFIX _)::xs =>
    resolve_nullprecs listrule (optmerge r closefix) xs
  | _ => raise Fail "resolve_nullprecs: can't happen"


fun resolve_same_precs rules =
  case rules of
    [] => []
  | [x] => [x]
  | ((p1 as SOME _, r1)::(rules1 as (p2, r2)::rules2)) => let
    in
      if p1 <> p2 then
        (p1, r1)::(resolve_same_precs rules1)
      else let
        val merged_rule = merge_rules (r1, r2)
          handle GrammarError s =>
            raise GrammarError (s ^ "(" ^Int.toString (valOf p1)^")")
      in
        (p1, merged_rule) :: resolve_same_precs rules2
      end
    end
  | ((NONE, _)::_) => resolve_nullprecs NONE NONE rules


infix Gmerge
(* only merges rules, keeps rest as in g1 *)
fun ((g1:grammar) Gmerge (g2:(int option * grammar_rule) list)) = let
  val g0_rules =
    Listsort.sort (fn (e1,e2) => aug_compare(#1 e1, #1 e2))
    (rules g1 @ g2)
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
  | LISTRULE rlist => null rlist
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
  fun lr_ok (ls:listspec) = #cons ls <> s andalso #nilstr ls <> s
  fun stringbinder LAMBDA = true
    | stringbinder (BinderString r) = #term_name r <> s
in
  case rule of
    SUFFIX (STD_suffix slist) => SUFFIX (STD_suffix (List.filter rr_ok slist))
  | INFIX (STD_infix(slist, assoc)) =>
      INFIX(STD_infix (List.filter rr_ok slist, assoc))
  | PREFIX (STD_prefix slist) => PREFIX (STD_prefix (List.filter rr_ok slist))
  | PREFIX (BINDER slist) => PREFIX (BINDER (List.filter stringbinder slist))
  | CLOSEFIX slist => CLOSEFIX (List.filter rr_ok slist)
  | LISTRULE rlist => LISTRULE (List.filter lr_ok rlist)
  | _ => rule
end


fun remove_tok {term_name, tok} r = let
  fun rels_safe rels = not (List.exists (fn e => e = TOK tok) rels)
  fun rr_safe ({term_name = s, elements,...}:rule_record) =
    s <> term_name orelse rels_safe (rule_elements elements)
  fun binder_safe b =
      case b of
        BinderString {term_name = tnm, tok = tk, ...} =>
          tk <> tok orelse tnm <> term_name
      | LAMBDA => true

in
  case r of
    SUFFIX (STD_suffix slist) =>
      SUFFIX (STD_suffix (List.filter rr_safe slist))
  | INFIX(STD_infix (slist, assoc)) =>
      INFIX (STD_infix (List.filter rr_safe slist, assoc))
  | PREFIX (STD_prefix slist) =>
      PREFIX (STD_prefix (List.filter rr_safe slist))
  | PREFIX (BINDER blist) =>
    PREFIX (BINDER (List.filter binder_safe blist))
  | CLOSEFIX slist => CLOSEFIX (List.filter rr_safe slist)
  | LISTRULE rlist => let
      fun lrule_ok (r:listspec) =
        (#cons r <> term_name andalso #nilstr r <> term_name)  orelse
        (first_tok (#leftdelim r) <> tok andalso
         first_tok (#rightdelim r) <> tok andalso
         first_tok (#separator r) <> tok)
    in
      LISTRULE (List.filter lrule_ok rlist)
    end
  | _ => r
end

fun remove_toklist {term_name, toklist} r = let
  fun relstoks rels = List.mapPartial (fn TOK s => SOME s | _ => NONE) rels
  fun rr_safe ({term_name = s, elements, ...} : rule_record) =
      s <> term_name orelse relstoks (rule_elements elements) <> toklist
  fun binder_safe b =
      case b of
        BinderString { term_name = s, tok, ...} => [tok] <> toklist orelse
                                                   s <> term_name
      | LAMBDA => true
in
  case r of
    SUFFIX (STD_suffix slist) => SUFFIX (STD_suffix (List.filter rr_safe slist))
  | INFIX (STD_infix (slist, assoc)) =>
      INFIX (STD_infix (List.filter rr_safe slist, assoc))
  | PREFIX (STD_prefix slist) => PREFIX (STD_prefix (List.filter rr_safe slist))
  | PREFIX (BINDER blist) => PREFIX (BINDER (List.filter binder_safe blist))
  | CLOSEFIX slist => CLOSEFIX (List.filter rr_safe slist)
  | LISTRULE rlist => let
      fun lrule_dies (r:listspec) =
          (#cons r = term_name orelse #nilstr r = term_name) andalso
          (relstoks (rule_elements (#leftdelim r)) = toklist orelse
           relstoks (rule_elements (#rightdelim r)) = toklist orelse
           relstoks (rule_elements (#separator r)) = toklist)
    in
      LISTRULE (List.filter (not o lrule_dies) rlist)
    end
  | _ => r
end

fun remove_standard_form G s = map_rules (remove_form s) G
fun remove_form_with_tok G r = map_rules (remove_tok r) G
fun remove_form_with_toklist r = map_rules (remove_toklist r)


fun rule_fixityToString f =
  case f of
    Infix(a,i) => "Infix("^assocToString a^", "^Int.toString i^")"
  | Closefix => "Closefix"
  | Suffix p => "Suffix "^Int.toString p
  | Prefix p => "Prefix "^Int.toString p


fun rrec2delta rf (rr : rule_record) = let
  val {term_name,paren_style,block_style,elements,...} = rr
in
  (#timestamp rr,
   GRULE {term_name = term_name, paren_style = paren_style,
          block_style = block_style, pp_elements = elements, fixity = rf})
end

fun rules_for G nm = let
  fun search_rrlist rf acc rrl = let
    fun recurse acc0 rrl =
        case rrl of
          [] => acc0
        | rr :: rest => recurse (if #term_name rr = nm then
                                   rrec2delta rf rr::acc0 else acc0)
                                rest
  in
    recurse acc rrl
  end
  fun search_blist acc blist =
      case blist of
        [] => acc
      | LAMBDA :: rest => search_blist acc rest
      | BinderString {tok,term_name,timestamp} :: rest =>
        if term_name = nm then
          search_blist
            ((timestamp, BRULE {term_name = term_name, tok = tok}) :: acc)
            rest
        else
          search_blist acc rest
  fun search_lslist acc lslist =
      case lslist of
        [] => acc
      | r :: rest => if #cons r = nm orelse #nilstr r = nm then
                       search_lslist ((0, LRULE r) :: acc) rest
                     else
                       search_lslist acc rest
  fun search acc rs =
      case rs of
        [] => List.rev acc
      | (fixopt, grule) :: rest => let
        in
          case grule of
            PREFIX (BINDER blist) => search (search_blist acc blist) rest
          | PREFIX (STD_prefix rrlist) =>
            search (search_rrlist (Prefix (valOf fixopt)) acc rrlist)
                   rest
          | SUFFIX (STD_suffix rrlist) =>
            search (search_rrlist (Suffix (valOf fixopt)) acc rrlist)
                   rest
          | INFIX (STD_infix (rrlist, assoc)) =>
            search (search_rrlist (Infix(assoc, valOf fixopt)) acc rrlist)
                   rest
          | CLOSEFIX rrl => search (search_rrlist Closefix acc rrl) rest
          | LISTRULE lsl => search (search_lslist acc lsl) rest
          | _ => search acc rest
        end
in
  search [] (rules G)
end

fun add_rule G0 {term_name = s : string, fixity = f, pp_elements,
                 paren_style, block_style} = let
  val _ =  pp_elements_ok pp_elements orelse
                 raise GrammarError "token list no good"
  val contending_tstamps = map #1 (rules_for G0 s)
  val new_tstamp = List.foldl Int.max 0 contending_tstamps + 1
  val rr = {term_name = s, elements = pp_elements, timestamp = new_tstamp,
            paren_style = paren_style, block_style = block_style}
  val new_rule =
    case f of
      Infix (a,p) => (SOME p, INFIX(STD_infix([rr], a)))
    | Suffix p => (SOME p, SUFFIX (STD_suffix [rr]))
    | Prefix p => (SOME p, PREFIX (STD_prefix [rr]))
    | Closefix => (NONE, CLOSEFIX [rr])
in
  G0 Gmerge [new_rule]
end

fun add_grule G0 r = G0 Gmerge [r]

fun add_binder {term_name,tok} G0 = let
  val contending_tstamps = map #1 (rules_for G0 term_name)
  val binfo = {term_name = term_name, tok = tok,
               timestamp = List.foldl Int.max 0 contending_tstamps + 1}
in
  G0 Gmerge [(SOME 0, PREFIX (BINDER [BinderString binfo]))]
end

fun add_listform G lrule = let
  fun ok_el e =
      case e of
        EndInitialBlock _ => false
      | BeginFinalBlock _ => false
      | RE TM => false
      | LastTM => false
      | FirstTM => false
      | _ => true
  fun check_els els =
      case List.find (not o ok_el) els of
        NONE => ()
      | SOME s => raise GrammarError "Invalid pp_element in listform"
  fun is_tok (RE (TOK _)) = true
    | is_tok _ = false
  fun one_tok pps =
    if length (List.filter is_tok pps) = 1 then ()
    else raise GrammarError "Must have exactly one TOK in listform elements"
  val {separator, leftdelim, rightdelim, ...} = lrule
  val _ = app check_els [separator, leftdelim, rightdelim]
in
  G Gmerge [(NONE, LISTRULE [lrule])]
end

fun add_delta ud G =
    case ud of
      GRULE r => add_rule G r
    | BRULE r => add_binder r G
    | LRULE r => add_listform G r

fun prefer_form_with_tok (r as {term_name,tok}) G0 = let
  val contending_timestamps = map #1 (rules_for G0 term_name)
  val newstamp = List.foldl Int.max 0 contending_timestamps + 1
in
  fupdate_rules
  (fupdate_rulelist
   (fupdate_rule_by_termtok r
                            (update_rr_tstamp newstamp)
                            (update_b_tstamp newstamp))) G0
end

fun prefer_form_with_toklist (r as {term_name,toklist}) G = let
  val contending_timestamps = map #1 (rules_for G term_name)
  val t' = List.foldl Int.max 0 contending_timestamps + 1
in
  G |> fupdate_rules (fupdate_rulelist
                        (fupdate_rule_by_termtoklist r
                                                     (update_rr_tstamp t')
                                                     (update_b_tstamp t')))
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

fun get_precedence (G:grammar) s = let
  val rules = rules G
  fun check_rule (p, r) = let
    fun elmem s [] = false
      | elmem s (({elements, ...}:rule_record)::xs) =
      Lib.mem (TOK s) (rule_elements elements) orelse elmem s xs
  in
    case r of
      INFIX(STD_infix (elms, assoc)) =>
        if elmem s elms then SOME(Infix(assoc, valOf p))
        else NONE
    | PREFIX(STD_prefix elms) =>
          if elmem s elms then SOME (Prefix (valOf p))
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

fun merge_specials S1 S2 = let
  val {type_intro = typ1, lambda = lam1, endbinding = end1,
       restr_binders = res1, res_quanop = resq1} = S1
  val {type_intro = typ2, lambda = lam2, endbinding = end2,
       restr_binders = res2, res_quanop = resq2} = S2
in
  if typ1 = typ2 andalso lam1 = lam2 andalso end1 = end2 andalso resq1 = resq2
  then
    {type_intro = typ1, lambda = lam1, endbinding = end1,
     restr_binders = Lib.union res1 res2, res_quanop = resq1}
  else
    raise GrammarError "Specials in two grammars don't agree"
end

fun merge_bmaps typestring keyprinter m1 m2 = let
  (* m1 takes precedence - arbitrarily *)
  fun foldfn (k,v,newmap) =
    (if isSome (Binarymap.peek(newmap, k)) then
       Feedback.HOL_WARNING "term_grammar" "merge_grammars"
       ("Merging "^typestring^" has produced a clash on key "^keyprinter k)
     else
       ();
     Binarymap.insert(newmap,k,v))
in
  Binarymap.foldl foldfn m2 m1
end

fun merge_user_printers (n1,ks1) (n2,_) = let
  fun foldthis (tm,k,f) (n,ks) =
      if Binaryset.member(ks,k) then (n,ks)
      else (Net.insert(tm,(tm,k,f)) n, Binaryset.add(ks, k))
in
   Net.itnet foldthis n2 (n1,ks1)
end

fun alist_merge al1 al2 = let
  (* could try to be smart here and preserve orderings in some circumstances *)
  fun foldthis ((k,v), acc) =
      case Lib.assoc1 k acc of
        NONE => (k,v) :: acc
      | SOME _ => acc
in
  List.rev (List.foldl foldthis (List.rev al1) al2)
end

fun merge_grammars (G1:grammar, G2:grammar) :grammar = let
  val g0_rules =
    Listsort.sort (fn (e1,e2) => aug_compare(#1 e1, #1 e2))
                  (rules G1 @ rules G2)
  val newrules = resolve_same_precs g0_rules
  val newspecials = merge_specials (specials G1) (specials G2)
  val new_numinfo = Lib.union (numeral_info G1) (numeral_info G2)
  val new_oload_info =
    Overload.merge_oinfos (overload_info G1) (overload_info G2)
  val new_ups = let
    val GCONS g1 = G1 and GCONS g2 = G2
  in
    merge_user_printers (#user_printers g1) (#user_printers g2)
  end
in
  GCONS {rules = newrules, specials = newspecials, numeral_info = new_numinfo,
         overload_info = new_oload_info, user_printers = new_ups,
         absyn_postprocessors = alist_merge (absyn_postprocessors G1)
                                            (absyn_postprocessors G2)}
end

(* ----------------------------------------------------------------------
 * Prettyprinting grammars
 * ---------------------------------------------------------------------- *)

datatype ruletype_info = add_prefix | add_suffix | add_both | add_nothing

fun prettyprint_grammar_rules tmprint pstrm (G :grammar) = let
  open Portable
  val {add_string, add_break, begin_block, end_block,
       add_newline,...} = with_ppstream pstrm

  fun pprint_rr m (rr:rule_record) = let
    val rels = rule_elements (#elements rr)
    val (pfx, sfx) =
      case m of
        add_prefix => ("", " TM")
      | add_suffix => ("TM ", "")
      | add_both => ("TM ", " TM")
      | add_nothing => ("", "")
    fun special_case s =
      if s = bracket_special then "just parentheses, no term produced"
      else if s = recsel_special then "record field selection"
      else if s = recupd_special then "record field update"
      else if s = recfupd_special then "functional record update"
      else if s = recwith_special then "record update"
      else s

    val tmid_suffix0 = "  ["^ special_case (#term_name rr)^"]"
    val tmid_suffix =
      case rels of
        [TOK s] => if s <> #term_name rr then tmid_suffix0 else ""
      | _ => tmid_suffix0
  in
    begin_block INCONSISTENT 2;
    add_string pfx;
    pr_list (fn (TOK s) => add_string ("\""^s^"\"") | TM => add_string "TM")
            (fn () => add_string " ") (fn () => ()) rels;
    add_string sfx;
    add_string tmid_suffix;
    end_block ()
  end


  fun pprint_rrl (m:ruletype_info) (rrl : rule_record list) = let
  in
    begin_block INCONSISTENT 0;
    pr_list (pprint_rr m) (fn () => add_string " |")
            (fn () => add_break(1,0)) rrl;
    end_block ()
  end

  fun print_binder b = let
    open Lib
    val bnames =
      case b of
        LAMBDA => map (fn s => (s,"")) (#lambda (specials G))
      | BinderString {term_name,tok,...} => [(tok,
                                              if tok = term_name then ""
                                              else " ["^term_name^"]")]
    val endb = quote (#endbinding (specials G))
    fun one_binder (s, tnminfo) =
        add_string (quote s ^ " <..binders..> " ^ endb ^ " TM" ^ tnminfo)
  in
    pr_list one_binder
            (fn () => add_string " |")
            (fn () => add_break (1,0))
            bnames
  end


  fun print_binderl bl = let
  in
    begin_block INCONSISTENT 0;
    pr_list print_binder (fn () => add_string " |")
            (fn () => add_break (1,0)) bl;
    end_block()
  end


  fun pprint_grule (r: grammar_rule) =
    case r of
      PREFIX (STD_prefix rrl) => pprint_rrl add_prefix rrl
    | PREFIX (BINDER blist) => print_binderl blist
    | SUFFIX (STD_suffix rrl) => pprint_rrl add_suffix rrl
    | SUFFIX TYPE_annotation => let
        val type_intro = #type_intro (specials G)
      in
        add_string ("TM \""^type_intro^"\" TY  (type annotation)")
      end
    | INFIX (STD_infix (rrl, a)) => let
        val assocstring =
          case a of
            LEFT => "L-"
          | RIGHT => "R-"
          | NONASSOC => "non-"
      in
        begin_block CONSISTENT 0;
        pprint_rrl add_both rrl;
        add_break (3,0);
        add_string ("("^assocstring^"associative)");
        end_block()
      end
    | INFIX RESQUAN_OP => let
        val rsqstr = #res_quanop (specials G)
      in
        add_string ("TM \""^rsqstr^
                    "\" TM (restricted quantification operator)")
      end
    | CLOSEFIX rrl => pprint_rrl add_nothing rrl
    | INFIX (FNAPP rrl) => let
      in
        begin_block CONSISTENT 0;
        add_string "TM TM  (function application)";
        case rrl of [] => ()
                  | _ => (add_string " |"; add_break(1,0);
                          pprint_rrl add_both rrl);
        add_break(3,0);
        add_string ("(L-associative)");
        end_block()
      end
    | INFIX VSCONS => add_string "TM TM  (binder argument concatenation)"
    | LISTRULE lrs => let
        fun pr_lrule ({leftdelim, rightdelim, separator, ...}:listspec) =
          add_string ("\""^first_tok leftdelim^"\" ... \""^
                      first_tok rightdelim^
                      "\"  (separator = \""^ first_tok separator^"\")")
      in
        begin_block CONSISTENT 0;
        pr_list pr_lrule (fn () => add_string " |")
                         (fn () => add_break(1,0)) lrs;
        end_block ()
      end

  fun print_whole_rule (intopt, rule) = let
    val precstr0 =
      case intopt of
        NONE => ""
      | SOME n => "("^Int.toString n^")"
    val precstr = StringCvt.padRight #" " 7 precstr0
  in
    begin_block CONSISTENT 0;
    add_string precstr;
    add_string "TM  ::=  ";
    pprint_grule rule;
    end_block()
  end

in
  pr_list print_whole_rule (fn () => ()) (fn () => add_break (1,0)) (rules G)
end

fun prettyprint_grammar tmprint pstrm (G :grammar) = let
  open Portable
  val {add_string, add_break, begin_block, end_block,
       add_newline,...} = with_ppstream pstrm
  fun uninteresting_overload (k,r:Overload.overloaded_op_info) =
    length (#actual_ops r) = 1 andalso
    #Name (Term.dest_thy_const (hd (#actual_ops r))) = k
      handle HOL_ERR _ => false andalso
    length (Term.decls k) = 1
  fun print_overloading oinfo0 =
    if List.all uninteresting_overload oinfo0 then ()
    else let
      open Lib infix ##
      fun nblanks n = String.implode (List.tabulate(n, (fn _ => #" ")))
      val oinfo1 = List.filter (not o uninteresting_overload) oinfo0
      val oinfo = Listsort.sort (String.compare o (#1 ## #1)) oinfo1
      val max =
        List.foldl (fn (oi,n) => Int.max(UTF8.size (#1 oi), n))
                   0
                   oinfo
      fun pr_ov (overloaded_op,
                (r as {actual_ops,...}:Overload.overloaded_op_info)) =
       let
        fun pr_name t = let
          val {Thy,Name,Ty} = Term.dest_thy_const t
        in
          case Term.decls Name of
            [] => raise Fail "term_grammar.prettyprint: should never happen"
          | [_] => add_string Name
          | _ => add_string (Thy ^ "$" ^ Name)
        end handle HOL_ERR _ => (add_string "(";
                                 trace ("types", 1)
                                       (tmprint (strip_overload_info G) pstrm)
                                       t;
                                 add_string ")")
      in
        begin_block INCONSISTENT 0;
        add_string (overloaded_op^
                    nblanks (max - UTF8.size overloaded_op)^
                    " -> ");
        add_break(1,2);
        begin_block INCONSISTENT 0;
        pr_list pr_name (fn () => ()) (fn () => add_break (1,0)) actual_ops;
        end_block();
        end_block()
      end
    in
      add_newline();
      add_string "Overloading:";
      add_break(1,2);
      begin_block CONSISTENT 0;
      pr_list pr_ov (fn () => ()) add_newline oinfo;
      end_block ()
    end
  fun print_user_printers printers = let
    fun pr (pat,nm,f) =
        (tmprint G pstrm pat; add_string ("       ->  "^nm))
  in
    if Net.size printers = 0 then ()
    else
      (add_newline();
       add_string "User printing functions:";
       add_newline();
       add_string "  ";
       begin_block INCONSISTENT 0;
       pr_list pr (fn () => ()) (fn () => add_newline())
               (Net.itnet cons printers []);
       end_block())
  end
in
  begin_block CONSISTENT 0;
  (* rules *)
  prettyprint_grammar_rules tmprint pstrm G;
  add_newline();
  (* known constants *)
  add_string "Known constants:";
  add_break(1,2);
  begin_block INCONSISTENT 0;
  pr_list add_string (fn () => ()) (fn () => add_break(1,0))
                     (Listsort.sort String.compare (known_constants G));
  end_block ();
  (* overloading *)
  print_overloading (Overload.oinfo_ops (overload_info G));
  print_user_printers (user_printers G);
  end_block ()
end

fun add_const (s,t) =
    fupdate_overload_info (Overload.add_overloading(s,t))
val min_grammar = let
  open Term Portable
in
  stdhol |> add_const ("==>", prim_mk_const{Name = "==>", Thy = "min"})
         |> add_const ("=", prim_mk_const{Name = "=", Thy = "min"})
         |> add_const ("@", prim_mk_const{Name = "@", Thy = "min"})
         |> add_binder {term_name="@", tok = "@"}

         (* Using the standard rules for infixes for ==> and = seems
            to result in bad pretty-printing of goals.  I think the
            following customised printing spec works better.  The crucial
            difference is that the blocking style is CONSISTENT rather than
            INCONSISTENT. *)
         |> C add_rule {term_name   = "==>",
                        block_style = (AroundSamePrec, (CONSISTENT, 0)),
                        fixity      = Infix(RIGHT, 200),
                        pp_elements = [HardSpace 1, RE (TOK "==>"),
                                       BreakSpace(1,0)],
                        paren_style = OnlyIfNecessary}
         |> C add_rule {term_name   = "=",
                        block_style = (AroundSamePrec, (CONSISTENT, 0)),
                        fixity      = Infix(NONASSOC, 100),
                        pp_elements = [HardSpace 1, RE (TOK "="),
                                       BreakSpace(1,0)],
                        paren_style = OnlyIfNecessary}

end
(* ----------------------------------------------------------------------
    encoding and decoding grammars to and from strings
   ---------------------------------------------------------------------- *)
open Coding
infix || >- >> >* >->

fun assoc_encode LEFT = "L"
  | assoc_encode RIGHT = "R"
  | assoc_encode NONASSOC = "N"
val assoc_reader =
    (literal "L" >> return LEFT) ||
    (literal "R" >> return RIGHT) ||
    (literal "N" >> return NONASSOC)

fun binfo_encode (brks,i) =
    (case brks of
       Portable.CONSISTENT => "C"
     | Portable.INCONSISTENT => "I") ^
    IntData.encode i
val binfo_reader =
    ((literal "C" >> return Portable.CONSISTENT) ||
     (literal "I" >> return Portable.INCONSISTENT)) >*
    IntData.reader

fun block_style_encode (pbs, binfo) =
    (case pbs of
       AroundEachPhrase => "H"
     | AroundSamePrec => "C"
     | AroundSameName => "M"
     | NoPhrasing => "N") ^
    binfo_encode binfo

val block_style_reader =
    ((literal "H" >> return AroundEachPhrase) ||
     (literal "C" >> return AroundSamePrec) ||
     (literal "M" >> return AroundSameName) ||
     (literal "N" >> return NoPhrasing)) >*
    binfo_reader

fun rule_element_encode rel =
    case rel of
      TOK s => "K" ^ StringData.encode s
    | TM => "M"
val rule_element_reader =
    (literal "K" >> map TOK StringData.reader) ||
    (literal "M" >> return TM)


fun paren_style_encode Always = "A"
  | paren_style_encode OnlyIfNecessary = "O"
  | paren_style_encode ParoundPrec = "C"
  | paren_style_encode ParoundName = "N"
  | paren_style_encode NotEvenIfRand = "R"
val paren_style_reader =
    (literal "A" >> return Always) ||
    (literal "O" >> return OnlyIfNecessary) ||
    (literal "C" >> return ParoundPrec) ||
    (literal "N" >> return ParoundName) ||
    (literal "R" >> return NotEvenIfRand)

fun ppel_encode ppel =
    case ppel of
      PPBlock (ppels, binfo) => "P" ^ String.concat
                                          (List.map ppel_encode ppels) ^
                                "X" ^ binfo_encode binfo
    | EndInitialBlock binfo => "E" ^ binfo_encode binfo
    | BeginFinalBlock binfo => "B" ^ binfo_encode binfo
    | HardSpace i => "H" ^ IntData.encode i
    | BreakSpace (x,y) => "S" ^ IntData.encode x ^ IntData.encode y
    | RE rel => "R" ^ rule_element_encode rel
    | LastTM => "L"
    | FirstTM => "F"
fun ppel_reader s =
    ((literal "P" >>
      map PPBlock ((many ppel_reader >-> literal "X") >* binfo_reader)) ||
     (literal "E" >> map EndInitialBlock binfo_reader) ||
     (literal "B" >> map BeginFinalBlock binfo_reader) ||
     (literal "H" >> map HardSpace IntData.reader) ||
     (literal "S" >> map BreakSpace (IntData.reader >* IntData.reader)) ||
     (literal "R" >> map RE rule_element_reader)) s



fun rrule_encode {term_name,elements,timestamp,block_style,paren_style} =
    String.concat (StringData.encode term_name ::
                   IntData.encode timestamp ::
                   block_style_encode block_style ::
                   paren_style_encode paren_style ::
                   (List.map ppel_encode elements @ ["E"]))
val rrule_reader = let
  fun f ((((term_name, timestamp), block_style), paren_style), elements) =
      {term_name = term_name, timestamp = timestamp,
       block_style = block_style, paren_style = paren_style,
       elements = elements}
in
  map f (StringData.reader >* IntData.reader >*
         block_style_reader >* paren_style_reader >*
         ((many ppel_reader >-> literal "E") || fail))
end

fun binder_encode b =
    case b of
      LAMBDA => "L"
    | BinderString{tok,term_name,timestamp} =>
        "B" ^ StringData.encode tok ^ StringData.encode term_name ^
        IntData.encode timestamp
val binder_reader = let
  fun f ((tok,term_name),timestamp) =
      BinderString {tok = tok, term_name = term_name,
                    timestamp = timestamp}
in
  (literal "L" >> return LAMBDA) ||
  (literal "B" >> (map f (StringData.reader >* StringData.reader >*
                          IntData.reader)))
end

fun RRL s rrl = String.concat (s :: List.map rrule_encode rrl)
fun pfxrule_encode prule =
    case prule of
      STD_prefix rrl => RRL "S" rrl
    | BINDER bl => String.concat ("B"::List.map binder_encode bl)
val pfxrule_reader =
    (literal "S" >> map STD_prefix (many rrule_reader)) ||
    (literal "B" >> map BINDER (many binder_reader))

fun sfxrule_encode srule =
    case srule of
      STD_suffix rrl => RRL "S" rrl
    | TYPE_annotation => "T"
val sfxrule_reader =
    (literal "S" >> map STD_suffix (many rrule_reader)) ||
    (literal "T" >> return TYPE_annotation)

fun ifxrule_encode irule =
    case irule of
      STD_infix (rrl,a) => RRL "S" rrl ^ assoc_encode a
    | RESQUAN_OP => "R"
    | VSCONS => "V"
    | FNAPP rrl => RRL "F" rrl
val ifxrule_reader =
    (literal "S" >> map STD_infix (many rrule_reader >* assoc_reader)) ||
    (literal "R" >> return RESQUAN_OP) ||
    (literal "V" >> return VSCONS) ||
    (literal "F" >> map FNAPP (many rrule_reader))

fun lspec_encode {separator, leftdelim, rightdelim, block_info, cons, nilstr} =
    String.concat (List.map ppel_encode separator) ^
    StringData.encode cons ^
    String.concat (List.map ppel_encode leftdelim) ^
    StringData.encode nilstr ^
    String.concat (List.map ppel_encode rightdelim) ^
    binfo_encode block_info

val lspec_reader = let
  fun f (((((separator,cons),leftdelim),nilstr),rightdelim),binfo) =
      {separator = separator, leftdelim = leftdelim, nilstr = nilstr,
       block_info = binfo, cons = cons, rightdelim = rightdelim}
in
  map f (many ppel_reader >* StringData.reader >* many ppel_reader >*
         StringData.reader >* many ppel_reader >* binfo_reader)
end

fun fixity_encode f =
    case f of
      Infix(a,p) => "I" ^ assoc_encode a ^ IntData.encode p
    | Suffix p => "S" ^ IntData.encode p
    | Prefix p => "P" ^ IntData.encode p
    | Closefix => "C"
val fixity_reader =
    (literal "I" >> map Infix (assoc_reader >* IntData.reader)) ||
    (literal "S" >> map Suffix IntData.reader) ||
    (literal "P" >> map Prefix IntData.reader) ||
    (literal "C" >> return Closefix)

fun user_delta_encode ud =
    case ud of
      GRULE {term_name, pp_elements, paren_style, block_style, fixity} =>
      String.concat ("G" :: StringData.encode term_name ::
                     paren_style_encode paren_style ::
                     block_style_encode block_style ::
                     fixity_encode fixity ::
                     List.map ppel_encode pp_elements @ ["X"])
    | BRULE {tok,term_name} =>
      "B" ^ StringData.encode tok ^ StringData.encode term_name
    | LRULE lspec => "L" ^ lspec_encode lspec

val user_delta_reader = let
  fun grule ((((tn,ps),bs),f),ppels) =
      GRULE {term_name = tn, paren_style = ps, block_style = bs, fixity = f,
             pp_elements = ppels}
  fun brule (tok,tn) = BRULE {tok = tok, term_name = tn}
in
  (literal "G" >> Coding.map grule (StringData.reader >*
                                    paren_style_reader >*
                                    block_style_reader >*
                                    fixity_reader >*
                                    many (ppel_reader) >-> literal "X")) ||
  (literal "B" >> Coding.map brule (StringData.reader >* StringData.reader)) ||
  (literal "L" >> Coding.map LRULE lspec_reader)
end



fun grule_encode grule =
    case grule of
      PREFIX pr => "P" ^ pfxrule_encode pr
    | SUFFIX sr => "S" ^ sfxrule_encode sr
    | INFIX ir => "I" ^ ifxrule_encode ir
    | CLOSEFIX rrl => String.concat ("C"::List.map rrule_encode rrl)
    | LISTRULE lspecl => String.concat ("L"::List.map lspec_encode lspecl)

val grule_reader =
    (literal "P" >> pfxrule_reader >- (return o PREFIX)) ||
    (literal "S" >> sfxrule_reader >- (return o SUFFIX)) ||
    (literal "I" >> ifxrule_reader >- (return o INFIX)) ||
    (literal "C" >> many rrule_reader >- (return o CLOSEFIX)) ||
    (literal "L" >> many lspec_reader >- (return o LISTRULE))


end; (* struct *)
