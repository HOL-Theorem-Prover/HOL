structure term_pp :> term_pp =
struct

open Portable HolKernel term_grammar
     HOLtokens HOLgrammars GrammarSpecials
     PrecAnalysis

infix >> >-

val PP_ERR = mk_HOL_ERR "term_pp";

fun PRINT s = print (s ^ "\n")
fun LEN l = Int.toString (length l)
fun option_to_string p NONE = "NONE"
  | option_to_string p (SOME x) = "SOME(" ^ p x ^ ")"

(*---------------------------------------------------------------------------
   Miscellaneous syntax stuff.
 ---------------------------------------------------------------------------*)

fun ellist_size els =
  let
    fun recurse A els =
      case els of
          [] => A
        | e::rest =>
          case e of
              PPBlock(more_els, (sty, ind)) => recurse A (more_els @ rest)
            | HardSpace n => recurse (A + n) rest
            | BreakSpace (n, m) => recurse 0 rest
            | RE (TOK s) => recurse (A + UTF8.size s) rest
            | _ => recurse 0 rest
  in
    recurse 0 els
  end

val dest_pair = sdest_binop (",", "pair") (PP_ERR "dest_pair" "");
val is_pair = Lib.can dest_pair;

fun isSuffix s1 s2 = (* s1 is a suffix of s2 *) let
  val ss = Substring.full s2
  val (pref, suff) = Substring.position s1 ss
in
  Substring.size suff = String.size s1
end

fun acc_strip_comb M rands =
 let val (Rator,Rand) = dest_comb M
 in acc_strip_comb Rator (Rand::rands)
 end
 handle HOL_ERR _ => (M,rands);

fun strip_comb tm = acc_strip_comb tm [];

fun string_of_nspaces n = String.concat (List.tabulate(n, (fn _ => " ")))
val isPrefix = String.isPrefix

fun lose_constrec_ty {Name,Ty,Thy} = {Name = Name, Thy = Thy}

(* while f is still of functional type, dest_abs the abs term and apply the
   f to the variable just stripped from the abs *)
fun apply_absargs f abs =
    if can dom_rng (type_of f) then let
        val (v, body) = dest_abs abs
      in
        apply_absargs (mk_comb(f, v)) body
      end
    else
      (f, abs)

(*---------------------------------------------------------------------------
       Type antiquotations (required in term parser)
 ---------------------------------------------------------------------------*)


val casesplit_munger = ref (NONE: (term -> term * (term * term)list) option)
fun init_casesplit_munger f =
    case !casesplit_munger of
      NONE => casesplit_munger := SOME f
    | _ => raise PP_ERR "init_casesplit_munger"
                        "casesplit munger already initialised"

exception CaseConversionFailed
fun convert_case tm =
    case !casesplit_munger of
      NONE => raise CaseConversionFailed
    | (SOME f) => let
        val (split_on, splits) = f tm
            handle HOL_ERR _ => raise CaseConversionFailed
        val _ = not (null splits) orelse raise CaseConversionFailed
      in
        (split_on, splits)
      end

val prettyprint_cases = ref true;
val prettyprint_cases_dt = ref false;
val _ = register_btrace ("pp_cases", prettyprint_cases)
val _ = register_btrace ("pp_cases_dt", prettyprint_cases_dt)

val {get = read_qblock_smash, ...} =
    create_trace {name = "PP.qblock_smash_limit", max = 1000,
                  initial = 4}

fun prettyprint_cases_name () =
    if !prettyprint_cases_dt then "dtcase" else "case";



(* ----------------------------------------------------------------------
    A flag controlling whether to print escaped syntax with a dollar
    or enclosing parentheses.  Thus whether the term mk_comb(+, 3) comes
    out as
      $+ 3
    or
      (+) 3
    The parser accepts either form.
   ---------------------------------------------------------------------- *)
open HOLPP smpp term_pp_types term_pp_utils

val dollar_escape = ref true

(* When printing with parentheses, make consecutive calls to the
   supplied printing function (add_string) so that the "tokens"
   aren't merged prematurely.  This is important to catch possible
   unwanted comment tokens.

   In the dollar-branch, we're happy to have the dollar smashed up
   against what follows it. *)
fun dollarise contentpfn parenpfn s =
    if !dollar_escape then contentpfn ("$" ^ s) >> return (UTF8.size s + 1)
    else parenpfn "(" >> contentpfn s >> parenpfn ")" >>
         return (UTF8.size s + 2)


val _ = Feedback.register_btrace ("pp_dollar_escapes", dollar_escape);

(* ----------------------------------------------------------------------
    Functions for manipulating the "printing info" data that is carried
    along by the monadic printer
   ---------------------------------------------------------------------- *)

open smpp term_pp_types term_pp_utils
infix || |||

val start_info = dflt_pinfo

fun getlaststring x =
    (fupdate (fn x => x) >-
     (fn (i:printing_info) => return (#last_string i)))
    x

fun setlaststring s = let
  fun set {seen_frees,current_bvars,last_string,in_gspec} =
      {seen_frees=seen_frees, current_bvars = current_bvars,
       last_string = s, in_gspec = in_gspec}
in
  fupdate set >> return ()
end


(* ----------------------------------------------------------------------
    Control symbol merging
   ---------------------------------------------------------------------- *)

(* A character is symbolic if it is listed on the first line of the
   symbolic characters given in DESCRIPTION, section 1.1.1(ii) (page 2).
   The function "Char.contains" is slow on the first argument, but
   fast on its second argument.
*)

val avoid_symbol_merges = ref true
val _ = register_btrace("pp_avoids_symbol_merges", avoid_symbol_merges)

fun creates_comment(s1, s2) = let
  val last = String.sub(s1, size s1 - 1)
  val first = String.sub(s2, 0)
in
  last = #"(" andalso first = #"*" orelse
  last = #"*" andalso first = #")"
end


fun avoid_symbolmerge G (add_string, add_xstring, add_break) = let
  open term_grammar
  val op>> = smpp.>>
  infix >>
  val keywords = #endbinding (specials G) :: grammar_tokens G @
                 known_constants G
  val split = term_tokens.user_split_ident keywords
  fun bad_merge (s1, s2) = let
    val combined = s1 ^ s2
    val (x,y) = split combined
  in
    y <> s2
  end handle base_tokens.LEX_ERR _ => true
  val rstr_quotes = [0x0022, 0x00BB, 0x203A]
  fun new_addxstring f (xstr as {s,sz,ann}) ls = let
    val allspaces = str_all (equal #" ") s
  in
    case s of
      "" => nothing
    | _ => (if ls = " " orelse allspaces then f xstr
            else if not (!avoid_symbol_merges) then f xstr
            else if mem (snd $ valOf $ UTF8.lastChar ls) rstr_quotes then f xstr
            (* special case the quotation because term_tokens relies on
               the base token technology (see base_lexer) to separate the
               end of a string from the next character *)
            else if creates_comment (ls, s) orelse bad_merge (ls, s) then
              add_string " " >> f xstr
            else
              f xstr) >>
           setlaststring (if allspaces then " " else s)
  end
  fun new_addstring f s = new_addxstring (fn{s,...}=>f s) {s=s,sz=NONE,ann=NONE}
  fun new_add_break (p as (n,m)) =
      (if n > 0 then setlaststring " " else nothing) >> add_break p
in
  ((fn s => getlaststring >- new_addstring add_string s),
   (fn xstr => getlaststring >- new_addxstring add_xstring xstr),
   new_add_break)
end


fun grav_name (Prec(n, s)) = s | grav_name _ = ""
fun grav_prec (Prec(n,s)) = n | grav_prec _ = ~1

fun pneeded_by_style (rr: term_grammar.rule_record, pgrav, fname, fprec) =
  case #paren_style rr of
    Always => true
  | OnlyIfNecessary => false
  | NotEvenIfRand => false
  | ParoundName => grav_name pgrav <> fname
  | ParoundPrec => grav_prec pgrav <> fprec
  | IfNotTop {realonly=true} => pgrav <> RealTop
  | IfNotTop {realonly=false} => pgrav <> RealTop andalso pgrav <> Top

fun countP P [] = 0
  | countP P (x::xs) = if P x then 1 + countP P xs else countP P xs
val numTMs = countP (fn TM => true | _ => false)

fun find_partial f  =
 let fun find [] = NONE
       | find (x::xs) =
           case f x
            of NONE => find xs
             | result => result
 in find end;


fun splitP P thelist = let
  fun with_acc acc [] = acc
    | with_acc (inlist, outlist) (x::xs) = let
      in
        if P x then with_acc (x::inlist, outlist) xs
        else with_acc (inlist, x::outlist) xs
      end
in
  with_acc ([], []) (List.rev thelist)
end

fun find_lspec els =
  let
    fun find_lspec1 e =
      case e of
          ListForm l => SOME l
        | PPBlock(els, _) => recurse els
        | _ => NONE
    and recurse els =
      case els of
          [] => NONE
        | e :: rest => (case find_lspec1 e of NONE => recurse rest | x => x)
  in
    recurse els
  end

fun grule_term_names G grule = let
  fun lift f (rr as {term_name,timestamp,elements,...}) =
    if term_name_is_lform term_name then
      case find_lspec elements of
          NONE => [] (* probably a bad rule *)
        | SOME {nilstr,cons,...} =>
            map (fn s => (s, (timestamp, f [rr]))) [nilstr, cons]
    else if term_name = GrammarSpecials.fnapp_special then []
    else
      [(term_name, (timestamp, f [rr]))]
  val suffix = lift (SUFFIX o STD_suffix)
  val prefix = lift (PREFIX o STD_prefix)
  fun mkifix a = lift (fn rrs => INFIX (STD_infix(rrs, a)))
  val closefix = lift CLOSEFIX
  fun bstamp LAMBDA = 0
    | bstamp (BinderString r) = #timestamp r
in
  case grule of
    PREFIX (STD_prefix list) => List.concat (map prefix list)
  | PREFIX (BINDER list) =>
      map (fn b => (binder_to_string G b, (bstamp b, PREFIX (BINDER [b])))) list
      (* binder_to_string is incomplete on LAMBDA, but this doesn't matter
         here as the information generated here is not used to print
         pure LAMBDAs *)
  | SUFFIX (STD_suffix list) => List.concat (map suffix list)
  | SUFFIX TYPE_annotation => []
  | INFIX (STD_infix(list, a)) => List.concat (map (mkifix a) list)
  | INFIX RESQUAN_OP => [(resquan_special, (0, grule))]
  | INFIX (FNAPP lst) =>
      (fnapp_special, (0, INFIX (FNAPP []))) ::
      List.concat (map (mkifix LEFT) lst)
  | INFIX VSCONS => [(vs_cons_special, (0, INFIX VSCONS))]
  | CLOSEFIX lst => List.concat (map closefix lst)
end

exception DoneExit

(* fun symbolic s = List.all HOLsym (String.explode s) *)

fun symbolic s = HOLsym (String.sub(s,String.size(s)-1));

(* term tm can be seen to have name s according to grammar G *)
fun has_name G s tm =
  grammar_name G tm = SOME s orelse
  (case dest_term tm of
       VAR(s', _) => s' = s
     | _ => false)

(* term tm might be the product of parsing name s -
   weaker than has_name *)
fun has_name_by_parser G s tm = let
  val oinfo = term_grammar.overload_info G
in
  case dest_term tm of
      VAR(vnm, _) => vnm = s orelse
                     (case dest_fakeconst_name vnm of
                          SOME{fake,...} => fake = s
                        | NONE => false)
    | _ =>
      (case Overload.info_for_name oinfo s of
           NONE => false
         | SOME {actual_ops,...} =>
             List.exists (fn t => can (match_term t) tm) actual_ops)
end

(* use of has_name_by_parser for nilstr allows for scenario where you have a
   chain of cons-like things, and cons does indeed want to print as the cons
   string, but the bottom nil equivalent would prefer to print some other way
   (perhaps with Unicode).
   In this scenario (e.g., in pred_sets, where EMPTY is the bottom of the
   list-form, but is overloaded to the Unicode symbol for empty set as well
   as the string "EMPTY"), you probably still want the list-form.
*)
fun is_list G (r as {nilstr, cons}) tm =
  has_name_by_parser G nilstr tm orelse
  (is_comb tm andalso
   let
     val (conshd, tail) = dest_comb tm
   in
     is_comb conshd andalso
     has_name G cons (rator conshd) andalso
     is_list G r tail
   end)

(*
val is_list = fn G => fn (r as {nilstr,cons}) => fn tm =>
              let
                val b = is_list G r tm
              in
                PRINT ("is_list{nilstr=\""^nilstr^"\",cons=\""^cons^"\"}" ^
                       debugprint G tm ^ " --> " ^ Bool.toString b);
                b
              end
*)

fun str_unicode_ok s = CharVector.all Char.isPrint s

fun overloads_to_string_form G = term_grammar.strlit_map G

fun oi_strip_comb' oinfo t =
    if current_trace "PP.avoid_unicode" = 0 then Overload.oi_strip_comb oinfo t
    else Overload.oi_strip_combP oinfo str_unicode_ok t

fun overloading_of_term' oinfo t =
    if current_trace "PP.avoid_unicode" = 0 then
      Overload.overloading_of_term oinfo t
    else
      Overload.overloading_of_termP oinfo str_unicode_ok t

fun pp_unicode_free ppel =
    case ppel of
        PPBlock(ppels, _) => List.all pp_unicode_free ppels
      | RE (TOK s) => str_unicode_ok s
      | ListForm {separator,...} => List.all pp_unicode_free separator
      | _ => true

fun is_unicode_ok_rule r =
    current_trace "PP.avoid_unicode" = 0 orelse
    (case r of
         PREFIX (STD_prefix rrs) =>
           List.all (fn {elements,...} => List.all pp_unicode_free elements)
                    rrs
       | PREFIX (BINDER bs) =>
         List.all (fn LAMBDA => true | BinderString {tok,...} => str_unicode_ok tok)
                  bs
       | SUFFIX TYPE_annotation => true
       | SUFFIX (STD_suffix rrs) =>
           List.all (fn {elements,...} => List.all pp_unicode_free elements)
                    rrs
       | INFIX (STD_infix (rrs, _)) =>
           List.all (fn {elements,...} => List.all pp_unicode_free elements)
                    rrs
       | INFIX (FNAPP rrs) =>
           List.all (fn {elements,...} => List.all pp_unicode_free elements)
                    rrs
       | INFIX VSCONS => true
       | INFIX RESQUAN_OP => true
       | CLOSEFIX rrs =>
           List.all (fn {elements,...} => List.all pp_unicode_free elements)
                    rrs)

fun rule_to_rr rule =
  case rule of
    INFIX (STD_infix (slist, _)) => slist
  | PREFIX (STD_prefix slist) => slist
  | SUFFIX (STD_suffix slist) => slist
  | CLOSEFIX slist => slist
  | _ => []

(* gives the "wrong" lexicographic order, but is more likely to
   resolve differences with one comparison because types/terms with
   the same name are rare, but it's quite reasonable for many
   types/terms to share the same theory *)
fun nthy_compare ({Name = n1, Thy = thy1}, {Name = n2, Thy = thy2}) =
  case String.compare(n1, n2) of
    EQUAL => String.compare(thy1, thy2)
  | x => x

val pp_print_firstcasebar = ref false
val _ = register_btrace ("PP.print_firstcasebar", pp_print_firstcasebar)

val unfakeconst = Option.map #fake o GrammarSpecials.dest_fakeconst_name

fun unsafe_style s =
    let
      open UTF8
      fun trans (CP c) =
          if c = 10(* NL *) then "\\n"
          else if c = 9 (* TAB *) then "\\t"
          else if c = 41 (* ")" *) then "\\)"
          else if UnicodeChars.isSpace_i c andalso c <> 32 (* SPC *) then
            String.translate
              (fn c => "\\" ^
                       StringCvt.padLeft #"0" 3 (Int.toString (Char.ord c)))
              (UTF8.chr c)
          else UTF8.chr c
        | trans (RB b) = "\\" ^ Int.toString b
      val scpts = safe_explode s
      val s' = String.concat (map trans scpts)
      val s'' = if not (null scpts) andalso last scpts = CP 42 (* * *) then
                  s' ^ "\\z"
                else s'
    in
      "$var$(" ^ s'' ^ ")"
    end
fun unicode_supdigit 0 = UnicodeChars.sup_0
  | unicode_supdigit 1 = UnicodeChars.sup_1
  | unicode_supdigit 2 = UnicodeChars.sup_2
  | unicode_supdigit 3 = UnicodeChars.sup_3
  | unicode_supdigit 4 = UnicodeChars.sup_4
  | unicode_supdigit 5 = UnicodeChars.sup_5
  | unicode_supdigit 6 = UnicodeChars.sup_6
  | unicode_supdigit 7 = UnicodeChars.sup_7
  | unicode_supdigit 8 = UnicodeChars.sup_8
  | unicode_supdigit 9 = UnicodeChars.sup_9
  | unicode_supdigit _ = raise Fail "unicode_supdigit: i < 0 or i > 9"
fun prettynumbers false i = Int.toString i
  | prettynumbers true i =
    let
      fun recurse A i =
          if i = 0 then String.concat A
          else
            recurse (unicode_supdigit (i mod 10) :: A) (i div 10)
    in
      if i = 0 then UnicodeChars.sup_0
      else if i < 0 then UnicodeChars.sup_minus ^ recurse [] (~i)
      else recurse [] i
    end

fun vname_styling unicode s =
    if not (Lexis.is_clean_varname s) then unsafe_style s
    else
      let val (s0,n) = Lib.extract_pc s
      in
        if n > 2 then s0 ^ "'" ^ prettynumbers unicode n ^ "'"
        else s
      end

fun atom_name tm = let
  val (vnm, _) = dest_var tm
in
  case unfakeconst vnm of
    NONE => vnm
  | SOME s => s
end handle HOL_ERR _ => fst (dest_const tm)

fun is_fakeconst tm = let
  val (vnm, _) = dest_var tm
in
  String.isPrefix GrammarSpecials.fakeconst_special vnm
end handle HOL_ERR _ => false

fun is_constish tm = is_const tm orelse is_fakeconst tm

fun pp_term (G : grammar) TyG backend = let
  val G = #tm_grammar_upd (#extras backend) G
  val TyG = #ty_grammar_upd (#extras backend) TyG
  val block = smpp.block
  fun tystr ty =
      PP.pp_to_string 10000
        (fn ty =>
            lower (type_pp.pp_type TyG PPBackEnd.raw_terminal ty) dflt_pinfo
              |> valOf |> #1)
        ty
  val {restr_binders,lambda,endbinding,type_intro,res_quanop} = specials G
  val overload_info = overload_info G
  val spec_table =
      HOLset.addList (HOLset.empty String.compare, grammar_tokens G)
  val num_info = numeral_info G
  fun insert ((nopt, grule), acc) = let
    val keys_n_rules = grule_term_names G grule
    val n = case nopt of SOME n => n | NONE => 0 (* doesn't matter *)
    fun sortinsert (tstamp,r) [] = [(n,tstamp,r)]
      | sortinsert (tstamp,r) ((h as (_,t',r')) :: rest) =
        if tstamp < t' then h :: sortinsert (tstamp,r) rest
        else (n,tstamp,r) :: h :: rest
    fun val_insert (tstamp,r) NONE = [(n,tstamp,r)]
      | val_insert (tstamp,r) (SOME l) = sortinsert (tstamp,r) l
    fun myinsert ((k, (tstamp, r)), acc) = let
      val existing = Binarymap.peek(acc, k)
      val newvalue =
        case existing of
          NONE => [(n,tstamp,r)]
        | SOME [] => [(n,tstamp,r)]
        | SOME ((old as (_,t',_))::rest) =>
          if tstamp > t' then (n,tstamp,r)::old::rest
          else old::(n,tstamp,r)::rest
    in
      Binarymap.insert(acc, k, newvalue)
    end
  in
    (List.foldl myinsert acc keys_n_rules)
  end
  val rule_table = List.foldl insert
                              (Binarymap.mkDict String.compare)
                              (term_grammar.rules G)
  fun lookup_term s = Binarymap.peek(rule_table, s)
  val comb_prec = #1 (hd (valOf (lookup_term fnapp_special)))
    handle Option =>
      raise PP_ERR "pp_term" "Grammar has no function application"
  val recsel_info = (* (precedence, upd_tok) option *)
    case lookup_term recsel_special of
      SOME [(n, _, INFIX (STD_infix([{elements = [RE(TOK s)],...}], _)))] =>
        SOME (n, s)
    | SOME _ =>
        raise PP_ERR "pp_term" "Invalid rule for record field select operator"
    | NONE => NONE
  val recupd_info = (* (precedence, upd_tok) option *)
    case lookup_term recupd_special of
      SOME [(n, _, INFIX (STD_infix([{elements = [RE(TOK s)],...}], _)))] =>
        SOME (Prec(n, recupd_special), s)
    | SOME _ =>
        raise PP_ERR "pp_term" "Invalid rule for record update operator"
    | NONE => NONE
  val recfupd_info = (* (precedence, with_tok) option *)
    case lookup_term recfupd_special of
      SOME [(n, _, INFIX (STD_infix([{elements = [RE(TOK s)],...}], _)))] =>
        SOME (Prec(n, recfupd_special), s)
    | SOME _ =>
        raise PP_ERR "pp_term" "Invalid rule for record f-update operator"
    | NONE => NONE
  val recwith_info = (* (precedence, with_tok) option *)
    case (lookup_term recwith_special) of
      SOME [(n, _, INFIX (STD_infix([{elements = [RE(TOK s)],...}], _)))] =>
        SOME (n, s)
    | SOME _ =>
        raise PP_ERR "pp_term"
          "Invalid form of rule for record with \"operator\""
    | NONE => NONE
  val reclist_info = (* (leftdelim, rightdelim, sep) option *)
    case lookup_term reccons_special of
      SOME [(_, _, CLOSEFIX[{elements,...}])] =>
      let
        fun find_listform pfx els =
          case els of
              [] => raise PP_ERR "pp_term" "No list-form in record literal rule"
            | ListForm{separator,...} :: rest =>
                (List.rev pfx, rest, separator)
            | e :: rest => find_listform (e::pfx) rest
      in
        SOME (find_listform [] elements)
      end
    | SOME _ =>
        raise PP_ERR "pp_term"
          "Invalid form of rule for record update list"
    | NONE => NONE


  val resquan_op_prec =
    case (lookup_term resquan_special) of
      SOME [] => raise Fail "term_pp : This really shouldn't happen"
    | SOME (x::xs) => SOME (#1 x)
    | NONE => NONE
  val vscons_prec = #1 (hd (valOf (lookup_term vs_cons_special)))
    handle Option =>
      raise PP_ERR "pp_term" "Grammar has no vstruct cons"
  val open_res_list_allowed =
    case resquan_op_prec of
      NONE => false
    | SOME p => p < vscons_prec

  val uprinters = user_printers G
  val printers_exist = FCNet.size uprinters > 0

  val my_dest_abs = term_pp_utils.pp_dest_abs G
  val my_is_abs = term_pp_utils.pp_is_abs G

  fun dest_vstruct bndr res t =
    term_pp_utils.dest_vstruct G {binder = bndr, restrictor = res} t



  fun strip_vstructs bndr res tm =
    term_pp_utils.strip_vstructs G {binder = bndr, restrictor = res} tm
  fun check_rrec_args f rrec args =
      (* checks that arguments link up with a rule-record suitably;
         this is not just whether or not there are the right number as
         arguments have to look list-ish if the rule-element is ListTM *)
      let
        val rels = f (rule_elements (#elements rrec))
        (*val _ = PRINT ("check_rrec_args: rels = [" ^
                               String.concatWith ", " (map reltoString rels) ^
                               "]; args = [" ^
                               String.concatWith ", " (map (debugprint G) args)^
                               "]")*)
        fun recurse rels args =
            case (rels, args) of
                ([], []) => true
              | ([], _) => false
              | (TM :: rrest, _ :: arest) => recurse rrest arest
              | (TOK _ :: rrest, _) => recurse rrest args
              | (_, []) => false
              | (ListTM {nilstr,cons,...} :: rrest, a :: arest)  =>
                is_list G {nilstr=nilstr,cons=cons} a andalso
                recurse rrest arest
      in
        recurse rels args
      end

  datatype comb_posn = RatorCP | RandCP | NoCP

  fun pr_term binderp showtypes showtypes_v ppfns combpos (tm:term)
              pgrav lgrav rgrav depth apps =
   let
    val full_pr_term = pr_term
    val pr_term = pr_term binderp showtypes showtypes_v ppfns combpos
    fun pr0 tm = pr_term0 binderp showtypes showtypes_v ppfns combpos tm
                          pgrav lgrav rgrav
                          depth
   in
     if printers_exist then
       let
         fun sysprint { gravs = (pg,lg,rg), binderp, depth} tm =
           full_pr_term binderp showtypes showtypes_v ppfns combpos tm
                        pg lg rg depth
         fun test (pat,_,_) = FCNet.can_match_term pat tm
         val candidates = filter test (FCNet.match tm uprinters)
         fun printwith f = f (TyG, G)
                             backend sysprint ppfns
                             (pgrav, lgrav, rgrav)
                             depth tm
         fun runfirst [] = pr0 tm
           | runfirst ((_, "", _) :: _) = pr0 tm
           | runfirst ((_,_,f)::t) =
                  (printwith f
                   handle UserPP_Failed => runfirst t) || runfirst t
       in
         runfirst candidates
       end
     else pr0 tm
   end apps
  and pr_term0 binderp showtypes showtypes_v ppfns combpos tm
               pgrav lgrav rgrav depth apps =
  let
    val full_pr_term = pr_term
    val pr_term = pr_term binderp showtypes showtypes_v ppfns NoCP
    val {add_string,add_break,add_xstring,...} = ppfns
    fun add_ann_string (s,ann) = add_xstring {s=s,ann=SOME ann,sz=NONE} >>
                                 return (UTF8.size s)
    fun uadd_ann_string x = add_ann_string x >> return ()
    fun var_ann t s = let
      val (vnm, ty) = dest_var t
      fun k bvs =
          add_ann_string(s,
                         ((if HOLset.member(bvs, t) then PPBackEnd.BV
                           else PPBackEnd.FV)
                          (ty, fn () => vnm ^ " :" ^ tystr ty)))
    in
      getbvs >- k
    end

    fun constann t s = let
      val (Thy,Name,Ty,fake) = let
        val {Thy,Name,Ty} = dest_thy_const t
      in
        (Thy,Name,Ty,Name)
      end handle HOL_ERR _ => let
            val (s, ty) = dest_var t
          in
            case GrammarSpecials.dest_fakeconst_name s of
                SOME{original = SOME{Thy,Name},fake} => (Thy,Name,ty,fake)
              | SOME{original = NONE, fake} => ("", fake, ty, fake)
              | NONE => raise mk_HOL_ERR "term_pp" "constann"
                              "Called on non-const (fake or o/wise)"
          end
      fun isAlphaNum_ish c = Char.isAlphaNum c orelse c = #"'" orelse c = #"_"
      val constr = if CharVector.all isAlphaNum_ish s then PPBackEnd.Const
                   else PPBackEnd.SymConst
    in
      add_ann_string(s, constr {Thy = Thy, Name = Name, Ty = (Ty, fn () => tystr Ty)})
    end
    fun block_by_style (rr, pgrav, fname, fprec) = let
      val needed =
        case #1 (#block_style (rr:rule_record)) of
          AroundSameName => grav_name pgrav <> fname
        | AroundSamePrec => grav_prec pgrav <> fprec
        | AroundEachPhrase => true
        | NoPhrasing => false
    in
      if needed then
        let
          val (c, i) = #2 (#block_style rr)
        in
          block c i
        end
      else
        I
    end
    fun paren b p =
      if b then
        block INCONSISTENT 1 (
          add_string "(" >> (p >- (fn r => add_string ")" >> return r))
        )
      else p

    fun spacep b = if b then add_break(1, 0) else nothing
    fun hardspace n = add_string (string_of_nspaces n)
    fun sizedbreak n = add_break(n, 0)

    fun doTy ty =
        type_pp.pp_type_with_depth TyG backend (decdepth depth) ty

    (* Prints "elements" from a concrete syntax rule.

         els is the list of pp_elements;
         args is a list of terms to be inserted in place of RE TM elements;
         fopt is a term corresponding to the constant (if any) at the head
           position of the term.

       Returns the unused args *)
    fun print_ellist fopt (lprec, cprec, rprec) (els, args : term list) = let
      (* val _ = PRINT
                 ("print_ellist: "^Int.toString (length els)^" elements; "^
                  " args = [" ^
                  String.concatWith ", " (map (debugprint G) args) ^ "]") *)
      fun onetok acc [] = acc
        | onetok NONE (RE (TOK s) :: rest) = onetok (SOME s) rest
        | onetok (SOME _) (RE (TOK s) :: rest) = NONE
        | onetok acc (_ :: rest) = onetok acc rest
      val tok_string =
          case (fopt, onetok NONE els) of
              (SOME f, SOME _) =>
                if is_constish f then constann f else var_ann f
            | _ => (fn s => add_string s >> return (UTF8.size s))
      fun addwidth (SOME n) a =
          a >- (fn (r,NONE) => return (r,NONE)
                | (r,SOME m) => return (r, SOME (m + n)))
        | addwidth NONE a = a >- (fn (r, _) => return (r, NONE))
      fun recurse (els, args) =
          case els of
            [] => return (args, SOME 0)
          | (e :: es) => let
              (* val _ = PRINT ("print_ellist.recurse.cons: "^
                             Int.toString (length args) ^ " args") *)
            in
              case e of
                PPBlock(more_els, (sty, ind)) =>
                  block sty ind (recurse (more_els,args)) >-
                  (fn (rest, nopt) => addwidth nopt (recurse (es,rest)))
              | HardSpace n =>
                  hardspace n >> addwidth (SOME n) (recurse (es, args))
              | BreakSpace (n, m) =>
                  add_break(n,m) >> addwidth NONE (recurse (es, args))
              | RE (TOK s) => (tok_string s >-
                               (fn m => addwidth (SOME m) (recurse (es, args))))
              | RE TM => (pr_term (hd args) Top Top Top (decdepth depth) >>
                          addwidth NONE (recurse (es, tl args)))
              | RE (ListTM _) => raise Fail "term_pp - encountered (RE ListTM)"
              | FirstTM =>
                  pr_term (hd args) cprec lprec cprec (decdepth depth) >>
                  addwidth NONE (recurse (es, tl args))
              | LastTM =>
                  pr_term (hd args) cprec cprec rprec (decdepth depth) >>
                  addwidth NONE(recurse (es, tl args))
              | EndInitialBlock _ => raise Fail "term_pp - encountered EIB"
              | BeginFinalBlock _ => raise Fail "term_pp - encountered BFB"
              | ListForm lspec =>
                  pr_lspec lspec (hd args) >-
                  (fn wopt => addwidth wopt (recurse (es, tl args)))
          end
      and pr_lspec (r as {nilstr, cons, block_info,...}) t =
          let
            (* val _ = PRINT ("pr_lspec: "^debugprint G t^" {nilstr=\""^nilstr^
                           "\"}")*)
            val sep = #separator r
            (* val (consistency, breakspacing) = block_info *)
            (* list will never be empty *)
            fun pr_list tm = let
              fun lrecurse depth tm = let
                val (_, args) = strip_comb tm
                val head = hd args
                  handle Empty => raise Fail ("pr_list empty list with t = "^
                                              debugprint G t)
                val tail = List.nth(args, 1)
              in
                if depth = 0 then add_string "..."
                else if has_name_by_parser G nilstr tail then
                  (* last element *)
                  pr_term head Top Top Top (decdepth depth)
                else let
                in
                  pr_term head Top Top Top (decdepth depth) >>
                  recurse (sep, []) >>
                  lrecurse (decdepth depth) tail
                end
              end
            in
              lrecurse depth t
            end
          in
            if has_name_by_parser G nilstr t then return (SOME 0)
            else pr_list t >> return NONE
          end
    in
      recurse (els, args) (* before
      PRINT "print_ellist terminated" *)
    end



    fun pr_vstruct bv = let
      val pr_t =
        if showtypes then full_pr_term true true showtypes_v ppfns NoCP
        else full_pr_term true false showtypes_v ppfns NoCP
    in
      case bv of
        Simple tm => let
        in
          if (is_pair tm orelse is_var tm) then
            record_bvars (free_vars tm)
                         (pr_t tm Top Top Top (decdepth depth))
          else
            raise PP_ERR "pr_vstruct"
              "Can only handle pairs and vars as vstructs"
        end
      | Restricted{Bvar, Restrictor} => let
        in
          block CONSISTENT 0
                (add_string "(" >>
                 pr_vstruct (Simple Bvar) >>
                 add_string (res_quanop) >>
                 add_break(0,2) >>
                 pr_term Restrictor Top Top Top (decdepth depth) >>
                 add_string ")")
        end
    end

    (* this function is only called in circumstances when all of a
       vstruct list is restricted with the same term and when the
       relative precedences of the res_quan_op (traditionally "::") is
       less than that of VSCONS.  If this situation pertains, then we
       can print out all of the vstruct items in a row, and then
       finish off with a single :: <tm>. For example \x y z::Q.

       The accompanying can_print_vstructl function spots when the
       situation as described above pertains.

       One final wrinkle has to be dealt with:
         The restricting term might have an occurrence in it of
         something that needs to be printed so that it looks like the
         endbinding token.  If this happens, then the restriction needs
         to be parenthesised.  In particular, the standard syntax has
         "." as the endbinding token and as the infix record selection
         operator, so that if you write
             !x y :: (rec.fld1). body
         the parenthesisation needs to be preserved.

         So, we have one last auxiliary function which determines whether
         or not the restrictor might print an endbinding token. *)

    infix might_print nmight_print
    fun tm nmight_print str = let
      val {Name,...} = dest_thy_const tm
      val actual_name0 =
        case overloading_of_term' overload_info tm of
          NONE => Name
        | SOME s => s
      fun testit s = if isPrefix s actual_name0 then SOME s else NONE
      val actual_name =
        case find_partial testit [recsel_special, recupd_special,
                                  recfupd_special] of
          NONE => actual_name0
        | SOME s => s
      val rule = lookup_term actual_name
    in
      case rule of
        NONE => Name = str
      | SOME rrlist =>
          List.exists (mem str o term_grammar.rule_tokens G o #3) rrlist
    end

    fun tm might_print str =
      case (dest_term tm) of
        COMB(Rator, Rand) => Rator might_print str orelse Rand might_print str
      | LAMB(_,Body) => Body might_print str
      | VAR(Name,Ty) => Name = str
      | CONST x => tm nmight_print str


    fun pr_res_vstructl restrictor res_op vsl body = let
      val bvts = map bv2term vsl
      val simples = map Simple bvts
      val add_final_parens = restrictor might_print endbinding
    in
      block CONSISTENT 2 (
        block INCONSISTENT 2 (pr_list pr_vstruct (add_break(1,0)) simples) >>
        add_string res_op >>
        paren add_final_parens (
          pr_term restrictor Top Top Top (decdepth depth)
        )
      ) >>
      add_string endbinding >> add_break (1,0) >>
      record_bvars (free_varsl bvts)
                   (block CONSISTENT 0
                          (pr_term body Top Top Top (decdepth depth)))
    end
    fun can_print_vstructl vsl = let
      fun recurse acc _ [] = SOME acc
        | recurse acc _ ((Simple _)::_) = NONE
        | recurse acc bvs (Restricted{Restrictor = t,Bvar}::xs) = let
          in
            if aconv t acc andalso List.all (fn v => not (free_in v t)) bvs then
              recurse acc (Bvar::bvs) xs
            else NONE
          end
    in
      case vsl of
        [] => raise PP_ERR "can_print_vstructl" "Empty list!"
      | (Simple _::xs) => NONE
      | (Restricted{Restrictor = t,Bvar}::xs) => recurse t [Bvar] xs
    end

    (* the pr_vstructl function figures out which way to print a given
       list of vstructs *)
    fun pr_vstructl vsl b =
      case can_print_vstructl vsl of
        SOME r => pr_res_vstructl r res_quanop vsl b
      | _ =>
        let
          fun recurse [] = raise Fail "pr_vstructl.recurse: Empty List!"
            | recurse [bv] =
                pr_vstruct bv >> add_string endbinding >> add_break (1,0) >>
                record_bvars (free_vars (bv2term bv))
                  (block CONSISTENT 0
                    (pr_term b Top Top Top (decdepth depth)))
            | recurse (bv::rest) =
                pr_vstruct bv >> add_break (1,0) >>
                record_bvars (free_vars (bv2term bv)) (recurse rest)
        in
          block INCONSISTENT 2 (recurse vsl)
        end

    fun pr_vstrblock (tok, _, vsl0) =
        let
          fun prv vs = (pr_vstruct vs >> addbvs (free_vars (bv2term vs)))
          fun mkSimple (Restricted{Bvar,...}) = Simple Bvar | mkSimple x = x
          val (vsl, finisher) =
              case can_print_vstructl vsl0 of
                  SOME r => (map mkSimple vsl0,
                             fn vs =>
                                getbvs >- (fn old =>
                                setbvs vs >>
                                add_string res_quanop >>
                                paren (r might_print endbinding) (
                                  pr_term r Top Top Top (decdepth depth)
                                ) >> setbvs old))
                | NONE => (vsl0, fn vs => nothing)
        in
          getbvs >- (fn old =>
          block INCONSISTENT 0 (
            tok >> pr_list prv (add_break(1,0)) vsl >> finisher old >>
            add_string endbinding
          ))
        end

    fun pr_abs tm = let
      val addparens = lgrav <> RealTop orelse rgrav <> RealTop
      val restr_binder =
          find_partial (fn (b,s) => if b = NONE then SOME s else NONE)
                       restr_binders
      val (bvars, body) = strip_vstructs NONE restr_binder tm
      val bvars_seen_here = List.concat (map (free_vars o bv2term) bvars)
      val lambda' = if current_trace "PP.avoid_unicode" > 0 then
                      List.filter str_unicode_ok lambda
                    else lambda
      val tok = case lambda' of
                    [] => raise PP_ERR "pr_abs" "No token for lambda abstraction"
                  | h::_ => h
    in
      paren addparens
            (block CONSISTENT 2 (add_string tok >> pr_vstructl bvars body))
    end

    fun can_pr_numeral stropt = List.exists (fn (k,s') => s' = stropt) num_info
    fun pr_numeral injtermopt tm = let
      open Overload
      val numty = Type.mk_thy_type {Tyop="num", Thy="num", Args=[]}
      val num2numty = numty --> numty
      val numinfo_search_string = Option.map (fst o dest_const) injtermopt
      val inj_t =
        case injtermopt of
          NONE => mk_thy_const {Name = nat_elim_term, Thy = "arithmetic",
                                Ty = numty --> numty}
        | SOME t => t
      val injty = type_of inj_t
      val is_a_real_numeral = (* i.e. doesn't need a suffix *)
          case info_for_name overload_info fromNum_str of
            NONE => false
          | SOME oi => op_mem aconv inj_t (#actual_ops oi)
      val numeral_str = Arbnum.toString (Literal.dest_numeral tm)
      val sfx =
          if not is_a_real_numeral orelse !Globals.show_numeral_types then let
              val (k, _) =
                  valOf (List.find (fn (_, s') => s' = numinfo_search_string)
                                   num_info)
            in
              str k
            end
          else ""
    in
      paren showtypes (
        add_ann_string (numeral_str ^ sfx,
                        PPBackEnd.Literal PPBackEnd.NumLit) >>
        (if showtypes then
           add_string (" "^type_intro) >>
           block INCONSISTENT (1 + UTF8.size (numeral_str ^ sfx) +
                               UTF8.size type_intro)
                 (doTy (#2 (dom_rng injty))) >>
           setlaststring " "
         else nothing)
      )
    end

    exception NotReallyARecord

    fun check_for_field_selection t1 t2 = let
      fun getfldname s =
          if isSome recsel_info then
            if isPrefix recsel_special s then
              SOME (String.extract(s, size recsel_special, NONE), t2)
            else NONE
          else NONE
    in
      if is_const t1 orelse is_fakeconst t1 then
        case grammar_name G t1 of
          SOME s => let
            val fldname = getfldname s
          in
            case fldname of
              SOME(fldname, t2) => let
                val (prec0, fldtok) = valOf recsel_info
                (* assumes that field selection is always left associative *)
                val add_l =
                    case lgrav of
                      Prec(n, _) => n >= prec0
                    | _ => false
                val add_r =
                    case rgrav of
                      Prec(n, _) => n > prec0
                    | _ => false
                val prec = Prec(prec0, recsel_special)
                val add_parens = add_l orelse add_r
                val lprec = if add_parens then Top else lgrav
                open PPBackEnd
              in
                block INCONSISTENT 0 (
                  paren add_parens (
                    pr_term t2 prec lprec prec (decdepth depth) >>
                    add_string fldtok >>
                    add_break(0,0) >>
                    add_ann_string (fldname, Literal FldName) >> return ()
                  )
                )
              end
            | NONE => fail
          end
        | NONE => fail
      else fail
    end

    fun check_for_record_update wholetm t1 t2 =
        if isSome recwith_info andalso isSome reclist_info andalso
           isSome recfupd_info andalso isSome recupd_info
        then let
            open Overload
            fun ap1 t = let val (d,_) = dom_rng (type_of t)
                        in mk_comb(t,genvar d) end
            fun ap2 t = t |> ap1 |> ap1
            val fupdhelper = Option.map (atom_name o #1) o
                             Overload.oi_strip_comb overload_info
            fun fupdstr0 wholetm_opt t =
              case wholetm_opt of
                  NONE => t |> ap2 |> fupdhelper
                | SOME t => t |> fupdhelper
            fun fupdstr wholetm_opt =
              Option.join o Lib.total (fupdstr0 wholetm_opt)
            (* function to determine if t is a record update *)
            fun is_record_update wholetm_opt t =
                if is_comb t andalso is_const (rator t) then
                  case fupdstr wholetm_opt (rator t) of
                      SOME s => isPrefix recfupd_special s
                    | NONE => false
                else false
            (* descend the rands of a term until one that is not a record
               update is found.  Return this and the list of rators up to
               this point. *)
            fun find_first_non_update acc t =
                if is_comb t andalso is_record_update NONE (rator t) then
                  find_first_non_update ((rator t)::acc) (rand t)
                else
                  (List.rev acc, t)
          fun categorise_update t = let
            (* t is an update. Here we generate
               a list of real updates (i.e., the terms corresponding to the
               new value in the update), each with an accompanying field
               string, and a boolean, which is true iff the update is a value
               update (not a "fupd") *)
            val (fld, value) = dest_comb t
            val rname = valOf (fupdstr NONE fld)
          in
            assert (isPrefix recfupd_special) rname
              handle HOL_ERR _ => raise NotReallyARecord;
            let
              val (f, x) = dest_comb value
              val {Thy, Name,...} = dest_thy_const f
              val fldname = String.extract(rname,size recfupd_special, NONE)
            in
              if Thy = "combin" andalso Name = "K" then [(fldname, x, true)]
              else [(fldname, value, false)]
            end handle HOL_ERR _ =>
                       [(String.extract(rname,size recfupd_special, NONE),
                         value, false)]
          end
        in
          if is_record_update (SOME wholetm) t1 then let
            val (updates0, base) = find_first_non_update [] t2
            val updates = List.concat (map categorise_update (t1::updates0))
            val (with_prec, with_tok) = valOf recwith_info
            val (ldelim, rdelim, sep) = valOf reclist_info
            fun print_update depth (fld, value, normal_upd) = let
              val (upd_prec, updtok) =
                if normal_upd then valOf recupd_info
                else valOf recfupd_info
            in
              block INCONSISTENT 2
                    (add_ann_string
                       (fld, PPBackEnd.Literal PPBackEnd.FldName) >>
                     add_string " " >>
                     add_string updtok >>
                     add_break(1,0) >>
                     pr_term value upd_prec upd_prec Top (decdepth depth))
            end
            fun print_updlist updates = let
              fun recurse depth upds =
                  if depth = 0 then add_string "..."
                  else
                    case upds of
                      [] => nothing (* should never happen *)
                    | [u] => print_update (decdepth depth) u
                    | u::us => (print_update (decdepth depth) u >>
                                print_ellist NONE (Top,Top,Top) (sep, []) >>
                                recurse (decdepth depth) us)
              val ldelim_size = ellist_size ldelim
            in
              block INCONSISTENT ldelim_size (
                print_ellist NONE (Top,Top,Top) (ldelim, []) >>
                recurse depth updates >>
                print_ellist NONE (Top,Top,Top) (rdelim, []) >> return ()
              )
            end
          in
            if is_const base andalso fst (dest_const base) = "ARB" then
              print_updlist updates
            else let
              val add_l =
                case lgrav of
                  Prec(n, _) => n > with_prec
                | _ => false
              val add_r =
                case rgrav of
                  Prec(n, _) => n > with_prec
                | _ => false
              val addparens = add_l orelse add_r
              val lprec = if addparens then Top else lgrav
              val with_grav = Prec(with_prec, recwith_special)
            in
              paren addparens (
                block INCONSISTENT 0 (
                  pr_term base with_grav lprec with_grav (decdepth depth) >>
                  add_string " " >>
                  add_string with_tok >>
                  add_break (1,0) >>
                  (if length updates = 1 then print_update depth (hd updates)
                   else print_updlist updates)
                )
              )
            end
          end handle NotReallyARecord => fail
          else fail
        end
        else fail

    fun comb_show_type (f, args) = let
      val _ = (showtypes andalso combpos <> RatorCP) orelse raise PP_ERR "" ""

      (* find out how the printer will map this constant into a string,
         and then see how this string maps back into constants.  The
         base_type will encompass the simulated polymorphism of the
         overloading system as well as any genuine polymorphism in
         the underlying constant. *)
      val base_ty = let
      in
        if is_fakeconst f then let
            (* f prints to the atom-name *)
            val nm = atom_name f
          in
            #base_type (valOf (Overload.info_for_name overload_info nm))
          end
        else
          case overloading_of_term' overload_info f of
            NONE => let
              val {Thy,Name,Ty} = dest_thy_const f
            in
              type_of (prim_mk_const {Thy = Thy, Name = Name})
            end
          | SOME print_name =>
            #base_type
              (valOf (Overload.info_for_name overload_info print_name))
      end
      val base_ptyM = Pretype.rename_typevars [] (Pretype.fromType base_ty)
      open errormonad
      fun foldthis (tm,acc) = let
        open Pretype
        val fn_ptyM = lift (fn ty => mk_fun_ty(fromType (type_of tm), ty))
                           new_uvar
      in
        acc >- (fn ty1 => fn_ptyM >- (fn ty2 => unify ty1 ty2 >> chase ty1))
      end
      val resultM = List.foldl foldthis base_ptyM args
    in
      case (resultM >- Pretype.has_unbound_uvar) Pretype.Env.empty of
          Error _ => false
        | Some (_, b) => b
    end handle HOL_ERR _ => false
             | Option => false

    fun pr_comb tm t1 t2 = let
      val add_l =
        case lgrav of
           Prec (n, _) => (n >= comb_prec)
         | _ => false
      val add_r =
        case rgrav of
          Prec (n, _) => (n > comb_prec)
        | _ => false
      val addparens = add_l orelse add_r

      val (f, args) = strip_comb tm
      val comb_show_type = comb_show_type(f,args)
      val prec = Prec(comb_prec, fnapp_special)
      val lprec = if addparens then Top else lgrav
      val rprec = if addparens then Top else rgrav
    in
      paren (addparens orelse comb_show_type) (
        block INCONSISTENT 0 (
          full_pr_term binderp showtypes showtypes_v ppfns RatorCP t1
                       prec lprec prec (decdepth depth) >>
          add_break (1, 2) >>
          full_pr_term binderp showtypes showtypes_v ppfns RandCP t2
                       prec prec rprec (decdepth depth) >>
          (if comb_show_type then
             add_string (" "^type_intro) >> add_break (0,0) >>
             doTy (type_of tm) >> setlaststring " "
           else nothing)
        )
      )
    end

    fun pr_sole_name tm n rules = let
      (* This function prints a solitary name n.  The rules are possibly
         relevant rules from the grammar.  If one is a list rule, and our
         n is the name of the nil case, then we should print that
         list's delimiters around nothing.
         Otherwise, the presence of a rule with our name n in it, is a
         probable indication that our name will need a $ printed out in
         front of it. *)
      (* monadically, it returns (best guess at) width of what it's just
         printed , SOME w, or NONE (for giving up on it) *)
      (* val _ = PRINT ("pr_sole_name: "^debugprint G tm) *)
      fun check_rule rule =
        case rule of
          CLOSEFIX [{elements,...}] =>
            (case find_lspec elements of
                NONE => NONE
              | SOME{nilstr,...} => if nilstr = n then SOME elements else NONE)
         | _ => NONE
      val nilrule = find_partial check_rule rules
      val ty = type_of tm
      fun add s =
        if is_constish tm then constann tm s
        else var_ann tm s
    in
      case nilrule of
        SOME els => ((* PRINT ("Found a nil-rule for "^n); *)
                     print_ellist NONE (Top,Top,Top) (els, [tm]) >-
                     (return o #2))
      | NONE => let
          (* if only rule is a list form rule and we've got to here, it
             will be a rule allowing this to the cons part of a list form.
             Such functions don't need to be dollar-ed *)
        in
          if HOLset.member(spec_table, n) then
            dollarise add add_string n >- (return o SOME)
          else add n >> return (SOME (UTF8.size n))
        end
    end

    datatype atomf_outcomes =
             AF_COMB of term * term * term
             | AF_ABS of term
             | AF_WITHRULE of grammar_rule *
                           {fprec : int, fname : string, f : term} *
                           term list (* args *) *
                           term (* Rand *)
             | AF_LIST of pp_element list * term
    fun pr_atomf (f,args0) = let
      (* the tm, Rator and Rand bindings that we began with are
               overridden by the f and args values that may be the product of
               oi_strip_comb.*)
      val fname = atom_name f
      (* val _ = PRINT ("pr_atomf: "^fname^" and "^
                           Int.toString (length args0) ^ " args") *)
      val tm = list_mk_comb (f, args0)
      val Rator = rator tm
      val (args,Rand) = front_last args0
      val candidate_rules =
          Option.map (List.filter (is_unicode_ok_rule o #3))
                     (lookup_term fname)
      (* val _ = PRINT ("pr_atomf: "^debugprint G tm^", "^
                           (case candidate_rules of
                               NONE => "rules = NONE"
                             | SOME l =>
                                 Int.toString (length l)^ " candidate rules"))
       *)


      val restr_binder =
          find_partial (fn (b,s) => if s=fname then SOME b else NONE)
                       restr_binders
      val restr_binder_rule =
          if isSome restr_binder andalso length args = 1 andalso
             my_is_abs Rand
          then let
            val bindex = case valOf restr_binder of
                             NONE => binder_to_string G LAMBDA
                           | SOME s => s
            val optrule = Option.map (List.filter (is_unicode_ok_rule o #3))
                                     (lookup_term bindex)
            fun ok_rule (_, _, r) =
                case r of
                    PREFIX(BINDER b) => true
                  | otherwise => false
          in
            case optrule of
                SOME (r::_) => if ok_rule r then SOME r else NONE
              | otherwise => NONE
          end
          else NONE
    in
      case candidate_rules of
          NONE =>
          let
          in
            case restr_binder of
                NONE => AF_COMB (tm, Rator, Rand)
              | SOME NONE =>
                if isSome restr_binder_rule then AF_ABS tm
                else AF_COMB(tm, Rator, Rand)
              | SOME (SOME fname) =>
                if isSome restr_binder_rule then
                  AF_WITHRULE(#3(valOf restr_binder_rule),
                              {fprec = #1 (valOf restr_binder_rule),
                               fname = fname,
                               f = f}, args, Rand)
                else
                  AF_COMB(tm, Rator, Rand)
          end
        | SOME crules0 =>
          let
            datatype ruletype = Norm of (int * grammar_rule)
                              | List of pp_element list
            fun suitable_rule (prec, _, rule) =
                case rule of
                    INFIX(STD_infix(rrlist, _)) =>
                    if check_rrec_args mkrels_infix (hd rrlist) args0 then
                      SOME (Norm(prec, rule))
                    else NONE
                  | INFIX RESQUAN_OP => raise Fail "Can't happen 90212"
                  | PREFIX (STD_prefix list) =>
                    if check_rrec_args mkrels_prefix (hd list) args0 then
                      SOME (Norm (prec, rule))
                    else NONE
                  | PREFIX (BINDER _) =>
                    if my_is_abs Rand andalso length args = 0 then
                      SOME (Norm(prec, rule))
                    else NONE
                  | SUFFIX (STD_suffix list) =>
                    if check_rrec_args mkrels_suffix (hd list) args0 then
                      SOME (Norm(prec, rule))
                    else NONE
                  | SUFFIX Type_annotation => raise Fail "Can't happen 90210"
                  | CLOSEFIX list =>
                    let
                      (* val _ = PRINT "suitable_rule: closefix check" *)
                      val r = hd list
                    in
                      if term_name_is_lform (#term_name r) then
                        ((* PRINT ("rule term-name is empty - testing " ^
                               debugprint G tm); *)
                          case find_lspec (#elements r) of
                              SOME {nilstr,cons,...} =>
                              if is_list G {nilstr=nilstr,cons=cons} tm then
                                SOME (List (#elements r))
                              else NONE
                            | NONE => NONE)
                      else if check_rrec_args mkrels_closefix r args0 then
                        SOME (Norm(prec, rule))
                      else NONE
                    end
                  | INFIX (FNAPP _) => raise Fail "Can't happen 90211"
                  | INFIX VSCONS => raise Fail "Can't happen 90213"
          in
            case List.mapPartial suitable_rule crules0 of
                Norm (prec,rule) :: _ =>
                AF_WITHRULE(rule, {fprec=prec, fname=fname, f=f}, args, Rand)
              | List els :: _ =>
                ((* PRINT "printing a List rule"; *)
                 AF_LIST(els, tm)
                )
              | [] => (*(PRINT "No suitable rules, printing with pr_comb";*)
                AF_COMB(tm, Rator, Rand)
                        (* before PRINT "Finished pr_comb") *)
          end
    end (* pr_atomf *)

    fun pr_comb_with_rule frule fterm args Rand = let
      val {fname,fprec,f} = fterm
      val comb_show_type = comb_show_type(f,args @ [Rand])
      fun ptype_block p =
          if comb_show_type then
            paren true (
              block CONSISTENT 0 (
                p >-
                (fn r => add_break (1,2) >> add_string type_intro >>
                         doTy (type_of tm) >> return r)
              )
            )
          else p
      fun block_up_els acc els =
        case els of
          [] => List.rev acc
        | (e::es) => let
          in
            case e of
              EndInitialBlock bi =>
                block_up_els [PPBlock(List.rev acc, bi)] es
            | BeginFinalBlock bi => let
                val block_of_rest = block_up_els [] es
              in
                List.rev (PPBlock(block_of_rest, bi)::acc)
              end
            | x => block_up_els (x::acc) es
          end
      val print_ellist = fn x => fn y => fn z => print_ellist x y z >> return ()
    in
      case frule of
        INFIX(STD_infix(lst, fassoc)) => let
          val rr = hd lst
          val elements = #elements rr
          fun check_grav a grav =
            case grav of
              Prec(n, _) =>
                (n > fprec) orelse (n = fprec andalso a <> fassoc)
            | _ => false
          val parens_needed_outright =
            check_grav RIGHT lgrav orelse check_grav LEFT rgrav
          val parens_needed_by_style =
            pneeded_by_style(rr, pgrav, fname, fprec)
          val addparens = parens_needed_outright orelse parens_needed_by_style
          val prec = Prec(fprec, fname)
          val lprec = if addparens then Top else lgrav
          val rprec = if addparens then Top else rgrav
          val arg_terms = args @ [Rand]
          val pp_elements = block_up_els [] ((FirstTM::elements) @ [LastTM])
          val begblock = block_by_style(rr, pgrav, fname, fprec)
        in
          ptype_block (
            paren (addparens orelse comb_show_type) (
              begblock
                (print_ellist (SOME f)
                              (lprec, prec, rprec)
                              (pp_elements, arg_terms))
            )
          )
        end
      | INFIX RESQUAN_OP => raise Fail "Res. quans shouldn't arise"
      | INFIX (FNAPP _) => raise PP_ERR "pr_term" "fn apps can't arise"
      | INFIX VSCONS => raise PP_ERR "pr_term" "vs cons can't arise"
      | SUFFIX (STD_suffix lst) => let
          val rr = hd lst
          val elements = #elements rr
          val parens_needed_outright =
            case lgrav of
              Prec(n, _) => n > fprec
            | _ => false
          val parens_needed_by_style =
            pneeded_by_style (rr, pgrav, fname, fprec)
          val addparens = parens_needed_outright orelse parens_needed_by_style
          val lprec = if addparens then Top else lgrav
          val prec = Prec(fprec, fname)
          val real_args = args @ [Rand]
          val pp_elements = block_up_els [] (FirstTM :: elements)
          val begblock =
            block_by_style(rr, pgrav, fname, fprec)
        in
          ptype_block (
            paren (addparens orelse comb_show_type) (
              begblock (
                print_ellist (SOME f)
                             (lprec, prec, Top)
                             (pp_elements, real_args)
              )
            )
          )
        end
      | SUFFIX TYPE_annotation =>
        raise Fail "Type annotation shouldn't arise"
      | PREFIX (STD_prefix lst) => let
          val rr = hd lst
          val elements = #elements rr
          val parens_needed_outright =
            case rgrav of
              Prec(n, _) => n > fprec
            | _ => false
          val addparens =
              parens_needed_outright orelse
              pneeded_by_style(rr, pgrav, fname, fprec) orelse
              (combpos = RandCP andalso #paren_style rr <> NotEvenIfRand)
          val rprec = if addparens then Top else rgrav
          val pp_elements = block_up_els [] (elements @ [LastTM])
          val real_args = args @ [Rand]
          val prec = Prec(fprec, fname)
          val begblock = block_by_style(rr, pgrav, fname, fprec)
        in
          ptype_block (
            paren (addparens orelse comb_show_type) (
              begblock (
                print_ellist (SOME f)
                             (Top, prec, rprec)
                             (pp_elements, real_args)
              )
            )
          )
        end
      | PREFIX (BINDER lst) =>
        let
          val addparens =
            case rgrav of
              Prec(n, _) => n > fprec
            | _ => false
          val addparens = addparens orelse combpos = RandCP
          fun strip_binderblocks lst f fname tm =
              let
                val tok = case hd lst of
                              LAMBDA => hd lambda (* should never happen *)
                            | BinderString r => #tok r
                fun find (bopt, s) = if bopt = SOME fname then SOME s else NONE
                val restr_binder = find_partial find restr_binders
                val (bvs, body) = strip_vstructs (SOME fname) restr_binder tm
                val bvars_seen_here =
                    List.concat (map (free_vars o bv2term) bvs)
                val addparens =
                    case rgrav of
                        Prec(n, _) => n > fprec
                      | _ => false
                val addparens = addparens orelse combpos = RandCP
                val print_tok = if is_constish f then constann f tok
                                else var_ann f tok
                val h = (print_tok, UTF8.size tok, bvs)
              in
                case total dest_comb body of
                    NONE => ([h], body)
                  | SOME (Rator,Rand) =>
                    let
                      val (f, args) = strip_comb Rator
                      val (oif, oiargs) =
                          case oi_strip_comb' overload_info body of
                              NONE => (f, args @ [Rand])
                            | SOME (f, args) => (f, args)
                    in
                      if is_abs f then ([h], body)
                      else
                        case pr_atomf (oif, oiargs) of
                            AF_WITHRULE(PREFIX(BINDER lst'), {fname,fprec,f}, _,
                                        _) =>
                            apfst (cons h)
                                  (strip_binderblocks lst' f fname body)
                          | _ => ([h], body)
                    end
              end
          val (binding_blocks, deep_body) = strip_binderblocks lst f fname tm
          fun dflt() =
            restore_bvars (
              paren (addparens orelse comb_show_type) (
                block INCONSISTENT 2 (
                  block INCONSISTENT 2 (
                    pr_list pr_vstrblock (add_break (1,0)) binding_blocks
                  ) >> add_break(1,0) >>
                        pr_term deep_body Top Top Top (decdepth depth)
                )
              )
            )
          val all_simple_vars = List.all (fn (_, _, vs) =>
                                             List.all (fn Simple v => is_var v
                                                      | _ => false) vs)
                                         binding_blocks
          fun vsize (Simple v, A) = UTF8.size (#1 (dest_var v)) + A
            | vsize (_,A) = A
          fun bsize1 (_, sz, vs) =
              sz (* qfier *) +
              UTF8.size endbinding +
              length vs (* spaces between vars + 1 after endbinding *) +
              List.foldl vsize 0 vs
        in
          if all_simple_vars andalso not showtypes_v andalso not showtypes then
            let
              val bsz =
                  List.foldl (fn (block,A) => bsize1 block + A) 0 binding_blocks
            in
              if bsz <= read_qblock_smash()
              then
                restore_bvars (
                  paren addparens (
                    block INCONSISTENT bsz (
                      pr_list pr_vstrblock (add_string " ") binding_blocks >>
                      add_string " " >>
                      pr_term deep_body Top Top Top (decdepth depth)
                    )
                  )
                )
              else dflt()
            end
          else dflt()
        end
      | CLOSEFIX lst => let
          val rr = hd lst
          val elements = #elements rr
        in
          ptype_block
            (uncurry block (#2 (#block_style rr))
               (print_ellist (SOME f)
                             (Top, Top, Top)
                             (elements, args @ [Rand]) >>
                return ()))
        end
    end

    fun execute_outcome afo =
        case afo of
            AF_COMB(t1,t2,t3) => pr_comb t1 t2 t3
          | AF_ABS t => pr_abs t
          | AF_WITHRULE (grule,frec,args,Rand) =>
              pr_comb_with_rule grule frec args Rand
          | AF_LIST (els, tm) =>
            (print_ellist NONE (Top,Top,Top) (els, [tm]) >> return ())



    fun print_ty_antiq tm = let
      val ty = parse_type.dest_ty_antiq tm
    in
      block CONSISTENT 2
            (add_string "(ty_antiq(" >>
             add_break(0,0) >>
             add_string "`:" >>
             doTy ty >>
             add_string "`))")
    end

    (* used to determine whether or not to print out disambiguating type
       information when showtypes_v is true *)
    fun const_is_polymorphic c =
        if is_const c then let
            val {Name,Thy,Ty} = dest_thy_const c
            val genconst = prim_mk_const {Name=Name,Thy=Thy}
          in
            Type.polymorphic (type_of genconst)
          end handle HOL_ERR _ => false
        (* the exception is possible if the constant is out of date *)
        else if is_fakeconst c then
          case Overload.info_for_name overload_info (atom_name c) of
            NONE => (* peculiar, printing but not parsing *) true
          | SOME {base_type,...} => Type.polymorphic base_type
        else false

    fun const_has_multi_ovl tm =
      case overloading_of_term' overload_info tm of
        NONE => (* no printing form *) true
      | SOME s =>
          case Overload.info_for_name overload_info s of
            NONE => true (* seems pretty unlikely *)
          | SOME {actual_ops,...} => length actual_ops > 1

    fun const_is_ambiguous t =
      const_is_polymorphic t orelse const_has_multi_ovl t

  in
    if depth = 0 then add_string "..."
    else if parse_type.is_ty_antiq tm then print_ty_antiq tm
    else
      case dest_term tm of
        VAR(vname, Ty) => let
          val (isfake, vname) =
              (true, valOf (unfakeconst vname))
              handle Option => (false, vname)
          val vrule = lookup_term vname
          fun add_type wopt =
              case wopt of
                  NONE =>
                    add_string (" "^type_intro) >>  add_break(0,0) >>
                    block INCONSISTENT 0 (doTy Ty) >> setlaststring " "
                | SOME i => add_string (" " ^ type_intro) >>
                            block INCONSISTENT (i + 1 + UTF8.size type_intro)
                                  (doTy Ty) >>
                            setlaststring " "
          fun new_freevar ({seen_frees,current_bvars,...}:printing_info) =
            showtypes andalso not isfake andalso
            not (HOLset.member(seen_frees, tm)) andalso
            not (HOLset.member(current_bvars, tm)) andalso not binderp
          fun calc_print_type nfv =
            showtypes_v orelse
            showtypes andalso not isfake andalso (binderp orelse nfv)
          val adds =
              if is_constish tm then constann tm else var_ann tm
          val uok = current_trace "PP.avoid_unicode" = 0
          val styled_name = if isfake then vname else vname_styling uok vname
        in
          fupdate (fn x => x) >- return o new_freevar >-
          (fn is_new =>
              (if is_new then spotfv tm else nothing) >>
              return (calc_print_type is_new)) >-
          (fn print_type =>
             block INCONSISTENT 0 (
               paren print_type (
                 (if isSome vrule then
                    pr_sole_name tm vname (map #3 (valOf vrule))
                  else
                    if HOLset.member(spec_table, vname) then
                      dollarise adds add_string styled_name >-
                      (return o SOME)
                    else adds styled_name >- (return o SOME)) >-
                 (fn w => if print_type then add_type w else nothing)
               )
             )
          )
        end
      | CONST(c as {Name, Thy, Ty}) => let
          val add_ann_string = constann tm
          fun add_prim_name() = add_ann_string (Thy ^ "$" ^ Name) >>
                                return (SOME (size Thy + size Name + 1))
          fun with_type action = let
          in
            if Name = "the_value" andalso Thy = "bool" then
              action() >> return ()
            else
              paren true (action() >- (fn wopt =>
                          add_string (" "^type_intro) >>
                          (case wopt of
                               NONE => add_break(0,0) >>
                                       block INCONSISTENT 0 (doTy Ty)
                             | SOME w =>
                                 block INCONSISTENT
                                       (w + UTF8.size type_intro + 1)
                                       (doTy Ty)) >>
                          setlaststring " "))
          end
          val r = {Name = Name, Thy = Thy}
          fun normal_const () = let
            fun cope_with_rules s = let
              val crules =
                  Option.map (List.filter (is_unicode_ok_rule o #3))
                             (lookup_term s)
              open PPBackEnd
            in
              if isSome crules then
                pr_sole_name tm s (map #3 (valOf crules))
              else if s = "0" andalso can_pr_numeral NONE then
                pr_numeral NONE tm >> return NONE
              else if Literal.is_emptystring tm then
                add_xstring {s="\"\"", sz = NONE,
                             ann = SOME (Literal StringLit)} >>
                return (SOME 2)
              else add_ann_string s >- (return o SOME)
            end
          in
            if Name = "the_value" andalso Thy = "bool" then let
                val {Args,...} = dest_thy_type Ty
              in (* TODO: annotate all of this as the constant somehow *)
                add_string "(" >>
                block CONSISTENT 0 (add_string type_intro >> doTy (hd Args)) >>
                add_string ")" >> return NONE
              end
            else
              case overloading_of_term' overload_info tm of
                NONE => add_prim_name()
              | SOME s =>
                (* term is overloaded *)
                if s = "case" then cope_with_rules Name
                else cope_with_rules s
          end
        in
          case (showtypes_v, const_is_polymorphic tm, const_has_multi_ovl tm) of
            (true, false, true) => add_prim_name() >> return ()
          | (true, true, true) => with_type add_prim_name
          | (true, true, false) => with_type normal_const
          | _ => if !show_types andalso combpos <> RatorCP andalso
                    const_is_polymorphic tm
                 then
                   with_type normal_const
                 else normal_const() >> return ()
        end
      | COMB(Rator, Rand) => let
          val (f, args) = strip_comb Rator
          val (oif, oiargs, overloadedp) =
              case oi_strip_comb' overload_info tm of
                NONE => (f, args @ [Rand], false)
              | SOME (f, args) => (f, args, true)

          fun is_atom tm = is_const tm orelse is_var tm
          fun maybe_pr_atomf () =
              if grammar_name G oif = SOME "case" then
                execute_outcome (pr_atomf (strip_comb tm))
              else if overloadedp then
                case oiargs of
                    [] => (* term is a comb, but it somehow overloads to a
                             single "constant" *)
                          pr_term oif pgrav lgrav rgrav depth
                  | _ => execute_outcome (pr_atomf (oif, oiargs))
              else if is_var f then
                execute_outcome (pr_atomf (f, args @ [Rand]))
              else pr_comb tm Rator Rand
        in
          (* check for various literal and special forms *)

          (* strings *)
          (case total Literal.dest_string_lit tm of
             NONE => fail
           | SOME s =>
             uadd_ann_string
               (Literal.string_literalpp {ldelim="\"", rdelim = "\""} s,
                PPBackEnd.Literal PPBackEnd.StringLit)) |||

          (* overloaded strings - with special designated rator to a rand
             which is in turn a string literal *)
          (fn _ => case total Literal.dest_string_lit (rand tm) of
                       SOME s =>
                       if is_constish f then
                         case overloads_to_string_form G {tmnm=atom_name f} of
                             NONE => fail
                           | SOME ldelim =>
                             uadd_ann_string
                               (Literal.string_literalpp
                                  (Literal.delim_pair {ldelim=ldelim})
                                  s,
                                PPBackEnd.Literal PPBackEnd.StringLit)
                       else fail
                     | NONE => fail) |||

          (* characters *)
          (fn _ => case total Literal.dest_char_lit tm of
             NONE => fail
           | SOME c => uadd_ann_string ("#" ^ Lib.mlquote (str c),
                                        PPBackEnd.Literal PPBackEnd.CharLit))|||

          (* numerals *)
          (fn _ => if Literal.is_numeral tm andalso can_pr_numeral NONE then
             pr_numeral NONE tm
           else fail) |||
          (fn _ => (if Literal.is_numeral Rand andalso
                       can_pr_numeral (SOME (atom_name Rator))
                    then pr_numeral (SOME Rator) Rand
                    else fail) handle HOL_ERR _ => fail) |||

          (* binders *)
          (fn _ => if my_is_abs tm then pr_abs tm else fail) |||

          (* record forms *)
          (fn _ =>
              case oiargs of
                [] => fail
              | _ => let
                  val (args, Rand) = front_last oiargs
                in
                  check_for_field_selection (list_mk_comb(oif,args)) Rand
                end) |||
          (fn _ => check_for_record_update tm Rator Rand) |||

          (* case expressions *)
          (fn () =>
              if (is_const f andalso (!prettyprint_cases)) then
                case grammar_name G oif of
                  SOME "case" =>
                  (let
                     val (split_on, splits) = convert_case tm
                     val parens = (case rgrav of Prec _ => true | _ => false)
                                  orelse
                                  combpos = RandCP
                     fun p body =
                         get_gspec >-
                         (fn b => if b orelse parens then
                                    block PP.CONSISTENT 1 (
                                      add_string "(" >>  body >> add_string ")"
                                    )
                                  else
                                    block PP.CONSISTENT 0 body)
                     val casebar =
                         add_break(1,0) >> add_string "|" >> hardspace 1
                     fun do_split rprec (l,r) =
                         record_bvars
                             (free_vars l)
                             (block PP.CONSISTENT 0 (
                                 pr_term l Top Top Top (decdepth depth) >>
                                 hardspace 1 >>
                                 add_string "=>" >> add_break(1,2) >>
                                 block PP.CONSISTENT 0
                                   (pr_term r Top Top rprec (decdepth depth)))
                             )
                   in
                     p (block PP.CONSISTENT 0
                            (add_string (prettyprint_cases_name ()) >>
                             add_break(1,2) >>
                             pr_term split_on Top Top Top (decdepth depth) >>
                             add_break(1,0) >> add_string "of") >>
                        (if !pp_print_firstcasebar then
                           casebar
                         else
                           add_break (1,2)) >>
                        (if length splits > 1 then
                           pr_list (do_split (Prec(0,"casebar")))
                              casebar (butlast splits) >>
                           casebar >>
                           do_split (if parens then Top else rgrav)
                              (last splits)
                         else
                           do_split (if parens then Top else rgrav)
                              (hd splits)))
                   end handle CaseConversionFailed => fail)
                | _ => fail
              else fail) |||

          (fn _ => if showtypes_v then
                     if const_is_ambiguous f then
                       pr_comb tm Rator Rand
                     else
                       maybe_pr_atomf()
                   else maybe_pr_atomf())
        end
      | LAMB(Bvar, Body) => pr_abs tm
  end apps
  val avoid_merge = avoid_symbolmerge G
  open PPBackEnd
in
  fn t =>
    let
      val {add_string,add_break,ublock,add_xstring,add_newline,ustyle,...} =
          backend
      val (add_string, add_xstring, add_break) =
          avoid_merge (add_string, add_xstring, add_break)
      val ppfns = {add_string = add_string,
                   add_xstring = add_xstring,
                   add_break = add_break,
                   add_newline = add_newline,
                   ublock = ublock,
                   ustyle = ustyle,
                   extras = ()}
    in
       ublock CONSISTENT 0 (
         pr_term false
                 (!Globals.show_types orelse !Globals.show_types_verbosely)
                 (!Globals.show_types_verbosely)
                 ppfns NoCP t RealTop RealTop RealTop
                 (!Globals.max_print_depth)
       )
    end
end

end; (* term_pp *)
