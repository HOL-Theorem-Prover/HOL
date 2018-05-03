structure term_grammar :> term_grammar =
struct

open HOLgrammars GrammarSpecials Lib Feedback term_grammar_dtype

val ERROR = mk_HOL_ERR "term_grammar"

type term = Term.term

type nthy_rec = {Name : string, Thy : string}

fun RE_compare (TOK s1, TOK s2) = String.compare(s1,s2)
  | RE_compare (TOK _, _) = LESS
  | RE_compare (TM, TOK _) = GREATER
  | RE_compare (TM, TM) = EQUAL
  | RE_compare (TM, ListTM _) = LESS
  | RE_compare (ListTM ls1, ListTM ls2) =
    let
      val {nilstr=n1,cons=c1,sep=s1} = ls1
      val {nilstr=n2,cons=c2,sep=s2} = ls2
      fun pcs cmp = pair_compare (String.compare, cmp)
    in
      pcs (pcs String.compare) ((n1,(c1,s1)), (n2,(c2,s2)))
    end
  | RE_compare (ListTM _, _) = GREATER

fun first_rtok rel =
  case rel of
      [] => raise Fail "PrecAnalysis.first_rtok: no token"
    | (TOK s :: _) => s
    | _ :: rest => first_rtok rest

fun first_tok ppel =
  case ppel of
      [] => raise Fail "PrecAnalysis.first_tok: no token"
    | p::rest =>
      (case p of
           PPBlock(pels, _) => first_tok (pels @ rest)
         | RE (TOK s) => s
         | ListForm lsp => first_tok (#separator lsp)
         | _ => first_tok rest)


fun rule_elements0 pplist acc =
  case pplist of
      [] => acc
    | ((RE x) :: xs) => acc |> cons x |> rule_elements0 xs
    | (PPBlock(pels, _) :: xs) =>
      acc |> rule_elements0 pels |> rule_elements0 xs
    | ListForm{separator, nilstr, cons=c, ...} :: xs =>
        acc |> cons (ListTM{nilstr=nilstr,cons=c,sep=first_tok separator})
            |> rule_elements0 xs
    | ( _ :: xs) => rule_elements0 xs acc
fun rule_elements ppels = List.rev (rule_elements0 ppels [])


  fun rels_ok [TOK _] = true
    | rels_ok (TOK _ :: TM :: xs) = rels_ok xs
    | rels_ok (TOK _ :: ListTM _ :: xs) = rels_ok xs
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
  | reltoString (ListTM _) = "ListTM"

fun pptoks ppels = List.mapPartial (fn TOK s => SOME s | _ => NONE)
                                   (rule_elements ppels)

(* used so that ProvideUnicode can look at additions to grammars and see if
   they involve Unicode *)
fun grule_toks ({pp_elements, ...}:grule) = pptoks pp_elements

(* ProvideUnicode wants to track term names of additions *)
fun grule_name ({term_name, ...}:grule) = term_name


type overload_info = Overload.overload_info

type ('a,'b) printer_info =
  (term * string * ('a,'b) term_pp_types.userprinter) FCNet.t *
  string Binaryset.set
type special_info = {type_intro : string,
                     lambda : string list,
                     endbinding : string,
                     restr_binders : (string option * string) list,
                     res_quanop : string}
fun fupd_lambda f {type_intro,lambda,endbinding,restr_binders,res_quanop} =
  {type_intro = type_intro, lambda = f lambda, endbinding = endbinding,
   restr_binders = restr_binders, res_quanop = res_quanop}


type prmP0 = Absyn.absyn -> Parse_supportENV.preterm_in_env

datatype grammar = GCONS of
  {rules : (int option * grammar_rule) list,
   specials : special_info,
   numeral_info : (char * string option) list,
   overload_info : overload_info,
   user_printers : (type_grammar.grammar * grammar, grammar) printer_info,
   absyn_postprocessors : (string * postprocessor) list,
   preterm_processors : (string*int,ptmprocessor) Binarymap.dict,
   next_timestamp : int
   }
and postprocessor = AbPP of grammar -> Absyn.absyn -> Absyn.absyn
and ptmprocessor = PtmP of grammar -> prmP0 -> prmP0

fun destAbPP (AbPP f) = f
fun destPtmP (PtmP f) = f

type absyn_postprocessor = grammar -> Absyn.absyn -> Absyn.absyn
type AbPTME = Absyn.absyn -> Parse_supportENV.preterm_in_env
type preterm_processor = grammar -> AbPTME -> AbPTME


datatype ruleset = GRS of (int option * grammar_rule) list * special_info
fun ruleset (GCONS {rules,specials,...}) = GRS (rules, specials)

type userprinter =
     (type_grammar.grammar * grammar, grammar) term_pp_types.userprinter

fun specials (GCONS G) = #specials G
fun numeral_info (GCONS G) = #numeral_info G
fun overload_info (GCONS G) = #overload_info G
fun known_constants (GCONS G) = Overload.known_constants (#overload_info G)
fun grammar_rules (GCONS G) = map #2 (#rules G)
fun rules (GCONS G) = (#rules G)
fun absyn_postprocessors0 (GCONS g) = #absyn_postprocessors g
fun absyn_postprocessors g = map (apsnd destAbPP) (absyn_postprocessors0 g)
fun gnext_timestamp (GCONS g) = #next_timestamp g

fun preterm_processor (GCONS g) k =
  Option.map destPtmP (Binarymap.peek(#preterm_processors g, k))


(* fupdates *)
open FunctionalRecordUpdate
fun gcons_mkUp z = makeUpdate8 z
fun update_G z = let
  fun from rules specials numeral_info overload_info user_printers
           absyn_postprocessors preterm_processors next_timestamp =
    {rules = rules, specials = specials, numeral_info = numeral_info,
     overload_info = overload_info, user_printers = user_printers,
     absyn_postprocessors = absyn_postprocessors,
     preterm_processors = preterm_processors, next_timestamp = next_timestamp}
  (* fields in reverse order to above *)
  fun from' next_timestamp preterm_processors absyn_postprocessors user_printers
            overload_info numeral_info specials rules =
    {rules = rules, specials = specials, numeral_info = numeral_info,
     overload_info = overload_info, user_printers = user_printers,
     absyn_postprocessors = absyn_postprocessors,
     preterm_processors = preterm_processors, next_timestamp = next_timestamp }
  (* first order *)
  fun to f {rules, specials, numeral_info,
            overload_info, user_printers, absyn_postprocessors,
            preterm_processors, next_timestamp} =
    f rules specials numeral_info overload_info user_printers
      absyn_postprocessors preterm_processors next_timestamp
in
  gcons_mkUp (from, from', to)
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

fun inc_timestamp (GCONS g) =
  GCONS (update_G g (U #next_timestamp (#next_timestamp g + 1)) $$)

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
          else (olddata, FCNet.insert(t,(t,nm,f)) newnet)
      val (data, newnet) = FCNet.itnet foldthis net (NONE, FCNet.empty)
      val newkeys = Binaryset.delete(keyset, k)
    in
      (GCONS (update_G g (U #user_printers (newnet,newkeys)) $$),
       data)
    end
  else (GCONS g, NONE)
end

fun add_user_printer (k,pat,v) g = let
  val (g', _) = remove_user_printer k g
  fun upd (net,keys) =
    (FCNet.insert(pat, (pat,k,v)) net, Binaryset.add(keys, k))
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
  GCONS (update_G g (U #absyn_postprocessors (update_alist (k,AbPP f) old)) $$)
end

fun remove_absyn_postprocessor k (GCONS g) = let
  val old = #absyn_postprocessors g
in
  case total (pluck (equal k o #1)) old of
    NONE => (GCONS g, NONE)
  | SOME ((_,AbPP f), rest) =>
    (GCONS (update_G g (U #absyn_postprocessors rest) $$), SOME f)
end

fun new_preterm_processor k f (GCONS g) = let
  val old = #preterm_processors g
in
  GCONS (update_G g
                  (U #preterm_processors (Binarymap.insert(old,k,PtmP f))) $$)
end

fun remove_preterm_processor k (G as GCONS g) = let
  val old = #preterm_processors g
in
  case Lib.total Binarymap.remove (old,k) of
      SOME(new, v) => (GCONS (update_G g (U #preterm_processors new) $$),
                       SOME (destPtmP v))
    | NONE => (G, NONE)
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
             CLOSEFIX [{term_name = "",
                        elements = [RE (TOK "<|"),
                                    ListForm {
                                      separator = [RE (TOK ";"),
                                                   BreakSpace(1,0)],
                                      block_info = (PP.INCONSISTENT, 0),
                                      cons = reccons_special,
                                      nilstr = recnil_special
                                    },
                                    RE (TOK "|>")],
                        timestamp = 0,
                        block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                        paren_style = OnlyIfNecessary}])],
   specials = {lambda = ["\\"], type_intro = ":", endbinding = ".",
               restr_binders = [], res_quanop = "::"},
   numeral_info = [],
   overload_info = Overload.null_oinfo,
   user_printers = (FCNet.empty, Binaryset.empty String.compare),
   absyn_postprocessors = [],
   preterm_processors =
     Binarymap.mkDict (pair_compare(String.compare, Int.compare)),
   next_timestamp = 1
   }

fun first_tok [] = raise Fail "Shouldn't happen: term_grammar.first_tok"
  | first_tok (RE (TOK s)::_) = s
  | first_tok (_ :: t) = first_tok t

local
  open stmonad
  infix >>
  fun add x acc = (x::acc, ())
  fun specials_from_elm [] = ok
    | specials_from_elm ((TOK x)::xs) = add x >> specials_from_elm xs
    | specials_from_elm (TM::xs) = specials_from_elm xs
    | specials_from_elm (ListTM {sep,...}::xs) = add sep >> specials_from_elm xs
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
  | _ => raise GrammarError "Attempt to have different forms at same level"

fun optmerge r NONE = SOME r
  | optmerge r1 (SOME r2) = SOME (merge_rules (r1, r2))

(* the listrule and closefix rules don't have precedences and sit at the
   end of the list.  When merging grammars, we will have a list of possibly
   intermingled closefix and listrule rules to look at, we want to produce
   just one closefix and one listrule rule for the final grammar *)

(* This allows for reducing more than just two closefix and listrules, but
   when merging grammars with only one each, this shouldn't eventuate *)
fun resolve_nullprecs closefix rules =
  case rules of
    [] => let
    in
      case closefix of
        NONE => [] (* should never really happen *)
      | SOME cf => [(NONE, cf)]
    end
  | (_, r as CLOSEFIX _)::xs =>
      resolve_nullprecs (optmerge r closefix) xs
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
  | ((NONE, _)::_) => resolve_nullprecs NONE rules


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
  | _ => rule
end


fun remove_tok P tok r = let
  fun rels_safe rels = not (List.exists (fn e => e = TOK tok) rels)
  fun rr_safe ({term_name = s, elements,...}:rule_record) =
    not (P s) orelse rels_safe (rule_elements elements)
  fun binder_safe b =
      case b of
        BinderString {term_name = tnm, tok = tk, ...} =>
          tk <> tok orelse not (P tnm)
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
  | _ => r
end

fun remove_standard_form G s = map_rules (remove_form s) G
fun remove_form_with_tok G {tok,term_name} =
  map_rules (remove_tok (fn s => s = term_name) tok) G
fun remove_form_with_toklist r = map_rules (remove_toklist r)
fun remove_rules_with_tok s =
  map_rules (remove_tok (fn _ => true) s)


fun fixityToString f =
  case f of
    Infix(a,i) => "Infix("^assocToString a^", "^Int.toString i^")"
  | Closefix => "Closefix"
  | Suffix p => "Suffix "^Int.toString p
  | Prefix p => "Prefix "^Int.toString p
  | Binder => "Binder"


fun rrec2delta rf (rr : rule_record) = let
  val {term_name,paren_style,block_style,elements,...} = rr
in
  (#timestamp rr,
   GRULE {term_name = term_name, paren_style = paren_style,
          block_style = block_style, pp_elements = elements,
          fixity = rf})
end

fun binder_grule {term_name,tok} =
  {term_name = term_name, paren_style = OnlyIfNecessary,
   block_style = (AroundEachPhrase, (PP.INCONSISTENT, 2)),
   pp_elements = [RE (TOK tok)], fixity = Binder}

fun extract_lspec rels =
  case rels of
      [] => NONE
    | ListTM l :: _ => SOME l
    | _ :: rest => extract_lspec rest

fun rules_for G nm = let
  fun search_rrlist rf acc rrl = let
    fun check rrec a =
      if #term_name rrec = nm then rrec2delta rf rrec :: a
      else if #term_name rrec = "" then
        case extract_lspec (rule_elements (#elements rrec)) of
            NONE => a
          | SOME {cons,nilstr,...} => if nm = cons orelse nilstr = nm then
                                        rrec2delta rf rrec :: a
                                      else a
      else a
    fun recurse acc rrl =
        case rrl of
          [] => acc
        | rr :: rest => recurse (check rr acc) rest
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
            ((timestamp, GRULE (binder_grule {term_name=term_name,tok=tok})) ::
             acc)
            rest
        else
          search_blist acc rest
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
          | _ => search acc rest
        end
in
  search [] (rules G)
end

fun add_rule {term_name = s : string, fixity = f, pp_elements,
              paren_style, block_style} G0 = let
  val _ =  pp_elements_ok pp_elements orelse
                 raise GrammarError "token list no good"
  val new_tstamp = gnext_timestamp G0
  val rr = {term_name = s, elements = pp_elements, timestamp = new_tstamp,
            paren_style = paren_style, block_style = block_style}
  val new_rule =
    case f of
      Infix (a,p) => (SOME p, INFIX(STD_infix([rr], a)))
    | Suffix p => (SOME p, SUFFIX (STD_suffix [rr]))
    | Prefix p => (SOME p, PREFIX (STD_prefix [rr]))
    | Closefix => (NONE, CLOSEFIX [rr])
    | Binder =>
      case pp_elements of
          [RE (TOK b)] => (SOME std_binder_precedence,
                           PREFIX(BINDER[BinderString{tok=b,term_name=s,
                                                      timestamp=new_tstamp}]))
        | _ => raise ERROR "add_rule" "Rules for binders must have one TOK only"

in
  inc_timestamp (G0 Gmerge [new_rule])
end

fun add_grule G0 r = G0 Gmerge [r]

fun add_binder {term_name,tok} G0 = let
  val binfo = {term_name = term_name, tok = tok,
               timestamp = gnext_timestamp G0 }
in
  inc_timestamp (G0 Gmerge [(SOME 0, PREFIX (BINDER [BinderString binfo]))])
end

fun listform_to_rule (lform : listspec) =
  let
    val {separator, leftdelim, rightdelim, cons, nilstr, ...} = lform
    val binfo = #block_info lform
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
    val _ = app check_els [separator, leftdelim, rightdelim]
    val _ = app one_tok [separator, leftdelim, rightdelim]
    val els =
        [PPBlock (leftdelim @ [ListForm { separator = separator,
                                          block_info = binfo,
                                          cons = cons, nilstr = nilstr}] @
                  rightdelim,
                  binfo)]
  in
    {term_name = "", pp_elements = els, fixity = Closefix,
     block_style = (AroundEachPhrase, binfo),
     paren_style = OnlyIfNecessary}
  end

fun add_listform G lrule = add_rule (listform_to_rule lrule) G

fun rename_to_fixity_field
      {rule_fixity,term_name,pp_elements,paren_style, block_style} =
  {fixity=rule_fixity, term_name = term_name, pp_elements = pp_elements,
   paren_style = paren_style, block_style = block_style}

fun standard_mapped_spacing {term_name,tok,fixity}  = let
  val bstyle = (AroundSamePrec, (PP.INCONSISTENT, 0))
  val pstyle = OnlyIfNecessary
  val ppels =
      case fixity of
        Infix _ => [HardSpace 1, RE (TOK tok), BreakSpace(1,0)]
      | Prefix _ => [RE(TOK tok), HardSpace 1]
      | Suffix _ => [HardSpace 1, RE(TOK tok)]
      | Closefix  => [RE(TOK tok)]
      | Binder => [RE(TOK tok)]
in
  {term_name = term_name, fixity = fixity, pp_elements = ppels,
   paren_style = pstyle, block_style = bstyle}
end

fun standard_spacing name fixity =
    standard_mapped_spacing {term_name = name, tok = name, fixity = fixity}

val std_binder_precedence = 0;

fun set_mapped_fixity {term_name,tok,fixity} G =
  let
    val nmtok = {term_name=term_name, tok = tok}
    val G = remove_form_with_tok G nmtok
  in
    case fixity of
        Binder => if term_name <> tok then
                    raise ERROR "set_mapped_fixity"
                          "Can't map binders to different strings"
                  else
                    add_binder nmtok G
      | rf => {fixity = rf, tok = tok, term_name = term_name}
                |> standard_mapped_spacing
                |> C add_rule G
  end


fun prefer_form_with_tok (r as {term_name,tok}) G0 = let
  val newstamp = gnext_timestamp G0
in
  G0 |> fupdate_rules
         (fupdate_rulelist
            (fupdate_rule_by_termtok r
                            (update_rr_tstamp newstamp)
                            (update_b_tstamp newstamp)))
     |> inc_timestamp
end

fun prefer_form_with_toklist (r as {term_name,toklist}) G = let
  val t' = gnext_timestamp G
in
  G |> fupdate_rules (fupdate_rulelist
                        (fupdate_rule_by_termtoklist r
                                                     (update_rr_tstamp t')
                                                     (update_b_tstamp t')))
    |> inc_timestamp
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
    | PREFIX (BINDER bs) =>
      find_partial
        (fn BinderString r => if #tok r = s then SOME Binder else NONE
          | LAMBDA => NONE)
        bs
    | SUFFIX (STD_suffix elms) => if elmem s elms then SOME (Suffix (valOf p))
                                  else NONE
    | CLOSEFIX elms => if elmem s elms then SOME Closefix else NONE
    | _ => NONE
  end
in
  if Lib.mem s (#lambda (specials G)) then SOME Binder
  else
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

structure userSyntaxFns = struct
  type 'a getter = string -> 'a
  type 'a setter = {name : string, code : 'a} -> unit
  type 'a t = 'a getter * 'a setter
  fun mk_table () =
    let
      val tab = ref (Binarymap.mkDict String.compare)
    in
      ((fn s => Binarymap.find(!tab, s)),
       (fn {name,code} => tab := Binarymap.insert(!tab, name, code)))
    end
  val (get_userPP, register_userPP) = mk_table() : userprinter t
  val (get_absynPostProcessor, register_absynPostProcessor) =
      mk_table() : absyn_postprocessor t
end

fun add_delta ud G =
    case ud of
      GRULE r => add_rule r G
    | RMTMTOK r => remove_form_with_tok G r
    | RMTMNM s => remove_standard_form G s
    | RMTOK s => remove_rules_with_tok s G
    | OVERLOAD_ON p => fupdate_overload_info (Overload.add_overloading p) G
    | IOVERLOAD_ON p =>
        fupdate_overload_info (Overload.add_inferior_overloading p) G
    | ASSOC_RESTR r => associate_restriction G r
    | RMOVMAP (s,kid) =>
        fupdate_overload_info (Overload.remove_mapping s kid) G
    | GRMOVMAP (s,tm) =>
        fupdate_overload_info (Overload.gen_remove_mapping s tm) G
    | MOVE_OVLPOSN {frontp,skid=(s,{Name,Thy})} =>
      let
        val oact = if frontp then Overload.bring_to_front_overloading
                   else Overload.send_to_back_overloading
      in
        fupdate_overload_info (oact {opname=s,realname=Name,realthy=Thy}) G
      end
    | ADD_NUMFORM cs => add_numeral_form G cs
    | CLR_OVL s =>
        fupdate_overload_info (#1 o Overload.remove_overloaded_form s) G
    | ADD_UPRINTER {codename = s, pattern} =>
      let
        val code = userSyntaxFns.get_userPP s
          handle Binarymap.NotFound =>
                 raise ERROR "add_delta"
                    ("No code named "^s^" registered for add user-printer")
      in
        add_user_printer (s,pattern,code) G
      end
    | ADD_ABSYN_POSTP {codename} =>
      let
        val code = userSyntaxFns.get_absynPostProcessor codename
          handle Binarymap.NotFound =>
                 raise ERROR "add_delta"
                       ("No code named "^codename^
                        " registered for add absyn-postprocessor")
      in
        new_absyn_postprocessor (codename, code) G
      end

fun add_deltas uds G = List.foldl (uncurry add_delta) G uds

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
      else (FCNet.insert(tm,(tm,k,f)) n, Binaryset.add(ks, k))
in
   FCNet.itnet foldthis n2 (n1,ks1)
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

fun bmap_merge m1 m2 =
  Binarymap.foldl (fn (k,v,acc) => Binarymap.insert(acc,k,v)) m1 m2

fun merge_grammars (G1 as GCONS g1, G2 as GCONS g2) :grammar = let
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
         absyn_postprocessors = alist_merge (absyn_postprocessors0 G1)
                                            (absyn_postprocessors0 G2),
         preterm_processors =
           bmap_merge (#preterm_processors g1) (#preterm_processors g2),
         next_timestamp = Int.max(#next_timestamp g1, #next_timestamp g2)}
end

(* ----------------------------------------------------------------------
 * Prettyprinting grammars
 * ---------------------------------------------------------------------- *)

datatype ruletype_info = add_prefix | add_suffix | add_both | add_nothing

fun prettyprint_grammar_rules tmprint (GRS(rules,specials)) = let
  open Portable HOLPP smpp

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
      else
        case dest_fakeconst_name s of
            NONE => s
          | SOME {fake,original = NONE} => "%" ^ fake ^ "%"
          | SOME {fake,original = SOME{Thy,Name}} =>
              Thy ^ "$" ^ Name ^ " - %" ^ fake ^ "%"

    val tmid_suffix0 = "  ["^ special_case (#term_name rr)^"]"
    val tmid_suffix =
      case rels of
        [TOK s] => if s <> #term_name rr then tmid_suffix0 else ""
      | _ => tmid_suffix0
  in
    block PP.INCONSISTENT 2 (
      add_string pfx >>
      pr_list (fn (TOK s) => add_string ("\""^s^"\"")
                | TM => add_string "TM"
                | ListTM {nilstr,cons,sep} =>
                  add_string ("LTM<" ^
                              String.concatWith "," [nilstr,cons,sep] ^
                              ">"))
              (add_string " ") rels >>
      add_string sfx >>
      add_string tmid_suffix
    )
  end


  fun pprint_rrl (m:ruletype_info) (rrl : rule_record list) =
    block PP.INCONSISTENT 0 (
      pr_list (pprint_rr m) (add_string " |" >> add_break(1,0)) rrl
    )

  fun print_binder b = let
    open Lib
    val bnames =
      case b of
        LAMBDA => map (fn s => (s,"")) (#lambda specials)
      | BinderString {term_name,tok,...} => [(tok,
                                              if tok = term_name then ""
                                              else " ["^term_name^"]")]
    val endb = quote (#endbinding specials)
    fun one_binder (s, tnminfo) =
        add_string (quote s ^ " <..binders..> " ^ endb ^ " TM" ^ tnminfo)
  in
    pr_list one_binder (add_string " |" >> add_break (1,0)) bnames
  end


  fun print_binderl bl =
    block PP.INCONSISTENT 0 (
      pr_list print_binder (add_string " |" >> add_break (1,0)) bl
    )


  fun pprint_grule (r: grammar_rule) =
    case r of
      PREFIX (STD_prefix rrl) => pprint_rrl add_prefix rrl
    | PREFIX (BINDER blist) => print_binderl blist
    | SUFFIX (STD_suffix rrl) => pprint_rrl add_suffix rrl
    | SUFFIX TYPE_annotation => let
        val type_intro = #type_intro specials
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
        block CONSISTENT 0 (
          pprint_rrl add_both rrl >>
          add_break (3,0) >>
          add_string ("("^assocstring^"associative)")
        )
      end
    | INFIX RESQUAN_OP => let
        val rsqstr = #res_quanop specials
      in
        add_string ("TM \""^rsqstr^
                    "\" TM (restricted quantification operator)")
      end
    | CLOSEFIX rrl => pprint_rrl add_nothing rrl
    | INFIX (FNAPP rrl) => let
      in
        block CONSISTENT 0 (
          add_string "TM TM  (function application)" >>
          (case rrl of [] => nothing
                     | _ => (add_string " |" >> add_break(1,0) >>
                             pprint_rrl add_both rrl)) >>
          add_break(3,0) >>
          add_string ("(L-associative)")
        )
      end
    | INFIX VSCONS => add_string "TM TM  (binder argument concatenation)"

  fun print_whole_rule (intopt, rule) = let
    val precstr0 =
      case intopt of
        NONE => ""
      | SOME n => "("^Int.toString n^")"
    val precstr = StringCvt.padRight #" " 7 precstr0
  in
    block CONSISTENT 0 (
      add_string precstr >>
      add_string "TM  ::=  " >>
      pprint_grule rule
    )
  end

in
  pr_list print_whole_rule (add_break (1,0)) rules
end

fun prettyprint_grammar tmprint (G :grammar) = let
  open Portable HOLPP smpp
  fun uninteresting_overload (k,r:Overload.overloaded_op_info) =
    length (#actual_ops r) = 1 andalso
    #Name (Term.dest_thy_const (hd (#actual_ops r))) = k
      handle HOL_ERR _ => false andalso
    length (Term.decls k) = 1
  fun print_overloading oinfo0 =
    if List.all uninteresting_overload oinfo0 then nothing
    else let
      open Lib infix ##
      fun nblanks n = CharVector.tabulate(n, fn _ => #" ")
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
        end handle HOL_ERR _ => (add_string "(" >>
                                 trace ("types", 1)
                                       (tmprint (strip_overload_info G))
                                       t >>
                                 add_string ")")
      in
        block INCONSISTENT 0 (
          add_string (overloaded_op^
                      nblanks (max - UTF8.size overloaded_op)^
                      " -> ") >>
          add_break(1,2) >>
          block INCONSISTENT 0 (pr_list pr_name (add_break (1,0)) actual_ops)
        )
      end
    in
      add_newline >>
      add_string "Overloading:" >>
      add_break(1,2) >>
      block CONSISTENT 0 (pr_list pr_ov add_newline oinfo)
    end
  fun print_user_printers printers = let
    fun pr (pat,nm,f) =
        (tmprint G pat >> add_string ("       ->  "^nm))
  in
    if FCNet.size printers = 0 then nothing
    else
      add_newline >>
      add_string "User printing functions:" >>
      add_newline >>
      add_string "  " >>
      block INCONSISTENT 0 (
        pr_list pr add_newline (FCNet.itnet cons printers [])
      )
  end
in
  block CONSISTENT 0 (
    (* rules *)
    prettyprint_grammar_rules tmprint (ruleset G) >> add_newline >>
    (* known constants *)
    add_string "Known constants:" >>
    add_break(1,2) >>
    block INCONSISTENT 0 (
      pr_list add_string (add_break(1,0))
              (Listsort.sort String.compare (known_constants G))
    ) >>
    (* overloading *)
    print_overloading (Overload.oinfo_ops (overload_info G)) >>
    print_user_printers (user_printers G)
  )
end

fun add_const (s,t) =
    fupdate_overload_info (Overload.add_overloading(s,t))
val min_grammar = let
  open Term Portable PP
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
         |> add_rule {term_name   = "==>",
                      block_style = (AroundSamePrec, (CONSISTENT, 0)),
                      fixity = Infix(RIGHT, 200),
                      pp_elements = [HardSpace 1, RE (TOK "==>"),
                                     BreakSpace(1,0)],
                      paren_style = OnlyIfNecessary}
         |> add_rule {term_name   = "=",
                      block_style = (AroundSamePrec, (CONSISTENT, 0)),
                      fixity = Infix(NONASSOC, 100),
                      pp_elements = [HardSpace 1, RE (TOK "="),
                                     BreakSpace(1,0)],
                      paren_style = OnlyIfNecessary}
         |> fupdate_specials (fupd_lambda (cons UnicodeChars.lambda))
end

(* ----------------------------------------------------------------------
    encoding and decoding grammars to and from strings
   ---------------------------------------------------------------------- *)
open Coding
infix || >- >> >* >->

fun binfo_encode (brks,i) =
    (case brks of
       PP.CONSISTENT => "C"
     | PP.INCONSISTENT => "I") ^
    IntData.encode i
val binfo_reader =
    ((literal "C" >> return PP.CONSISTENT) ||
     (literal "I" >> return PP.INCONSISTENT)) >*
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
    | ListTM{nilstr,cons,sep} =>
        "L" ^ StringData.encode nilstr ^ StringData.encode cons ^
        StringData.encode sep
val rule_element_reader =
    (literal "K" >> map TOK StringData.reader) ||
    (literal "M" >> return TM) ||
    (literal "L" >>
     map (fn ((n,c),s) => ListTM {nilstr=n,cons=c,sep=s})
         (StringData.reader >* StringData.reader >* StringData.reader))

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
    | ListForm lspec => "I" ^ lspec_encode lspec
    | LastTM => "L"
    | FirstTM => "F"
and lspec_encode {separator, block_info, cons, nilstr} =
    String.concat (List.map ppel_encode separator) ^
    StringData.encode cons ^
    StringData.encode nilstr ^
    binfo_encode block_info


fun ppel_reader s =
    ((literal "P" >>
      map PPBlock ((many ppel_reader >-> literal "X") >* binfo_reader)) ||
     (literal "E" >> map EndInitialBlock binfo_reader) ||
     (literal "B" >> map BeginFinalBlock binfo_reader) ||
     (literal "H" >> map HardSpace IntData.reader) ||
     (literal "S" >> map BreakSpace (IntData.reader >* IntData.reader)) ||
     (literal "R" >> map RE rule_element_reader) ||
     (literal "I" >> map ListForm lspec_reader) ||
     (literal "L" >> return LastTM) ||
     (literal "F" >> return FirstTM)
    ) s
and lspec_reader s = let
  fun f (((separator,cons),nilstr),binfo) =
      {separator = separator, nilstr = nilstr, block_info = binfo, cons = cons}
in
  map f (many ppel_reader (* sep *) >* StringData.reader (* cons *) >*
         StringData.reader (* nil *) >* binfo_reader (* binfo *)) s
end

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

fun fixity_encode f =
    case f of
      Infix(a,p) => "I" ^ assoc_encode a ^ IntData.encode p
    | Suffix p => "S" ^ IntData.encode p
    | Prefix p => "P" ^ IntData.encode p
    | Closefix => "C"
    | Binder => "B"
val fixity_reader =
    (literal "I" >> map Infix (assoc_reader >* IntData.reader)) ||
    (literal "S" >> map Suffix IntData.reader) ||
    (literal "P" >> map Prefix IntData.reader) ||
    (literal "C" >> return Closefix) ||
    (literal "B" >> return Binder)

fun grule_encode (gr : grule) =
  let
    val {term_name, pp_elements, paren_style, block_style, fixity} = gr
  in
    String.concat (StringData.encode term_name ::
                   paren_style_encode paren_style ::
                   block_style_encode block_style ::
                   fixity_encode fixity ::
                   List.map ppel_encode pp_elements @ ["X"])
  end

val grule_reader : grule Coding.reader = let
  fun grule ((((tn,ps),bs),f),ppels) =
      {term_name = tn, paren_style = ps, block_style = bs,
       fixity = f, pp_elements = ppels}
in
  Coding.map grule (StringData.reader >* paren_style_reader >*
                    block_style_reader >* fixity_reader >*
                    many (ppel_reader) >-> literal "X")
end

fun skid_encode (s, {Name,Thy}) =
  StringData.encode s ^ StringData.encode Name ^ StringData.encode Thy
val skid_reader =
    Coding.map (fn ((s,n),thy) => (s,{Name=n,Thy=thy}))
               (StringData.reader >* StringData.reader >* StringData.reader)

fun user_delta_encode write_tm ud =
    case ud of
      ADD_ABSYN_POSTP {codename} => "AAPP" ^ StringData.encode codename
    | ADD_NUMFORM (c,s) =>
        "AN" ^ CharData.encode c ^ OptionData.encode StringData.encode s
    | ADD_UPRINTER{codename=s,pattern=tm} =>
        "AUP" ^ StringData.encode s ^ StringData.encode (write_tm tm)
    | ASSOC_RESTR {binder,resbinder} =>
        "AR" ^ OptionData.encode StringData.encode binder ^
        StringData.encode resbinder
    | CLR_OVL s => "COV" ^ StringData.encode s
    | GRMOVMAP(s,tm) =>
        "RMG" ^ StringData.encode s ^ StringData.encode (write_tm tm)
    | GRULE gr => "G" ^ grule_encode gr
    | IOVERLOAD_ON (s,t) =>
        "OI" ^ StringData.encode s ^ StringData.encode (write_tm t)
    | MOVE_OVLPOSN {frontp,skid} =>
        "MOP" ^ BoolData.encode frontp ^ skid_encode skid
    | OVERLOAD_ON (s,t) =>
        "OO" ^ StringData.encode s ^ StringData.encode (write_tm t)
    | RMOVMAP skid => "RMO" ^ skid_encode skid
    | RMTMNM s => "RN" ^ StringData.encode s
    | RMTMTOK {term_name,tok} =>
        "RK" ^ StringData.encode term_name ^ StringData.encode tok
    | RMTOK s => "RMT" ^ StringData.encode s


fun user_delta_reader read_tm = let
in
  (literal "AAPP" >>
   Coding.map (fn s => ADD_ABSYN_POSTP {codename = s}) StringData.reader) ||
  (literal "AN" >>
   Coding.map ADD_NUMFORM
     (CharData.reader >* OptionData.reader StringData.reader)) ||
  (literal "AR" >>
   Coding.map (fn (b,rb) => ASSOC_RESTR {binder = b, resbinder = rb})
              (OptionData.reader StringData.reader >* StringData.reader)) ||
  (literal "AUP" >>
   Coding.map (fn (s,p) => ADD_UPRINTER {codename = s, pattern = p})
              (StringData.reader >* Coding.map read_tm StringData.reader)) ||
  (literal "COV" >> Coding.map CLR_OVL StringData.reader) ||
  (literal "G" >> Coding.map GRULE grule_reader) ||
  (literal "MOP" >>
   Coding.map (fn (frontp,skid) => MOVE_OVLPOSN {frontp=frontp,skid=skid})
              (BoolData.reader >* skid_reader)) ||
  (literal "OI" >>
   Coding.map IOVERLOAD_ON
     (StringData.reader >* Coding.map read_tm StringData.reader)) ||
  (literal "OO" >>
   Coding.map OVERLOAD_ON
     (StringData.reader >* Coding.map read_tm StringData.reader)) ||
  (literal "RK" >>
   Coding.map (fn (nm,tok) => RMTMTOK {term_name = nm, tok = tok})
              (StringData.reader >* StringData.reader)) ||
  (literal "RMG" >>
   Coding.map GRMOVMAP
              (StringData.reader >* Coding.map read_tm StringData.reader)) ||
  (literal "RMO" >> Coding.map RMOVMAP skid_reader) ||
  (literal "RMT" >> Coding.map RMTOK StringData.reader) ||
  (literal "RN" >> Coding.map RMTMNM StringData.reader)
end



fun grammar_rule_encode grule =
    case grule of
      PREFIX pr => "P" ^ pfxrule_encode pr
    | SUFFIX sr => "S" ^ sfxrule_encode sr
    | INFIX ir => "I" ^ ifxrule_encode ir
    | CLOSEFIX rrl => String.concat ("C"::List.map rrule_encode rrl)

val grammar_rule_reader =
    (literal "P" >> pfxrule_reader >- (return o PREFIX)) ||
    (literal "S" >> sfxrule_reader >- (return o SUFFIX)) ||
    (literal "I" >> ifxrule_reader >- (return o INFIX)) ||
    (literal "C" >> many rrule_reader >- (return o CLOSEFIX))


fun debugprint G tm =
  let
    open HolKernel
    val pr = debugprint G
    val map = List.map
  in
    case dest_term tm of
        VAR (s,_) => s
      | CONST {Name,Thy,...} =>
        Thy ^ "$" ^ Name ^ "<" ^
        (case grammar_name G tm of NONE => "" | SOME s => s) ^ ">"
      | COMB _ =>
        let
          val (f, args) = strip_comb tm
        in
          "(" ^ pr f ^ " " ^ String.concatWith " " (map pr args) ^ ")"
        end
      | LAMB _ =>
        let
          val (vs, bod) = strip_abs tm
        in
          "(\\" ^ String.concatWith " " (map pr vs) ^ ". " ^ pr bod ^ ")"
        end
  end

(** quick-and-dirty removal of all "non-trivial" overloadings **)

(* add overloading of constant and its name *)
fun grm_self_ovl (tm : term, tmG : grammar) =
  let val (str, ty) = Term.dest_const tm ;
  in fupdate_overload_info (Overload.add_overloading (str, tm)) tmG end ;

(* add in overloading of all constants with their names *)
fun self_ovl_all_consts (tmG : grammar) =
  List.foldr grm_self_ovl tmG (Term.all_consts ()) ;

(* clear all overloading info in a term grammar *)
fun clear_all_overloads (tmG : grammar) =
  fupdate_overload_info (fn _ => Overload.null_oinfo) tmG ;

fun clear_overloads (tmG : grammar) =
  self_ovl_all_consts (clear_all_overloads tmG) ;

end; (* struct *)
