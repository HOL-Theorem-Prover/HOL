structure term_pp :> term_pp =
struct

open Portable HolKernel term_grammar
     HOLtokens HOLgrammars GrammarSpecials;

val PP_ERR = mk_HOL_ERR "term_pp";

(*---------------------------------------------------------------------------
   Miscellaneous syntax stuff.
 ---------------------------------------------------------------------------*)

val dest_pair = sdest_binop (",", "pair") (PP_ERR "dest_pair" "");
val is_pair = Lib.can dest_pair;

fun mk_pair (fst,snd) = let
  val fsty = type_of fst
  val sndty = type_of snd
  val commaty = fsty --> sndty -->
                mk_thy_type{Tyop="prod",Thy="pair",Args=[fsty,sndty]}
  val c = mk_thy_const{Name=",", Thy="pair", Ty = commaty}
in
  list_mk_comb(c,[fst,snd])
end;

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
    case casesplit_munger of
      ref NONE => casesplit_munger := SOME f
    | _ => raise PP_ERR "init_casesplit_munger"
                        "casesplit munger already initialised"

exception CaseConversionFailed
fun convert_case tm =
    case casesplit_munger of
      ref NONE => raise CaseConversionFailed
    | ref (SOME f) => let
        val (split_on, splits) = f tm
            handle HOL_ERR _ => raise CaseConversionFailed
        val _ = not (null splits) orelse raise CaseConversionFailed
      in
        (split_on, splits)
      end

val prettyprint_cases = ref true;
val _ = register_btrace ("pp_cases", prettyprint_cases)

(* ----------------------------------------------------------------------
    A flag controlling whether to print escaped syntax with a dollar
    or enclosing parentheses.  Thus whether the term mk_comb(+, 3) comes
    out as
      $+ 3
    or
      (+) 3
    The parser accepts either form.
   ---------------------------------------------------------------------- *)
open smpp term_pp_types term_pp_utils

val dollar_escape = ref true

(* When printing with parentheses, make consecutive calls to the
   supplied printing function (add_string) so that the "tokens"
   aren't merged prematurely.  This is important to catch possible
   unwanted comment tokens.

   In the dollar-branch, we're happy to have the dollar smashed up
   against what follows it. *)
fun dollarise contentpfn parenpfn s =
    if !dollar_escape then contentpfn ("$" ^ s)
    else parenpfn "(" >> contentpfn s >> parenpfn ")"


val _ = Feedback.register_btrace ("pp_dollar_escapes", dollar_escape);

(* ----------------------------------------------------------------------
    Functions for manipulating the "printing info" data that is carried
    along by the monadic printer
   ---------------------------------------------------------------------- *)

open smpp term_pp_types term_pp_utils
infix || |||

val start_info = {seen_frees = empty_tmset, current_bvars = empty_tmset,
                  last_string = " ", in_gspec = false}

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
  fun new_addxstring f (xstr as {s,sz,ann}) ls = let
    val allspaces = str_all (equal #" ") s
  in
    case s of
      "" => nothing
    | _ => (if ls = " " orelse allspaces then f xstr
            else if not (!avoid_symbol_merges) then f xstr
            else if String.sub(ls, size ls - 1) = #"\"" then f xstr
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



(* ----------------------------------------------------------------------
    A flag controlling printing of set comprehensions
   ---------------------------------------------------------------------- *)

val unamb_comp = ref false
val _ = Feedback.register_btrace ("pp_unambiguous_comprehensions", unamb_comp)

fun grav_name (Prec(n, s)) = s | grav_name _ = ""
fun grav_prec (Prec(n,s)) = n | grav_prec _ = ~1


fun pneeded_by_style (rr: term_grammar.rule_record, pgrav, fname, fprec) =
  case #paren_style rr of
    Always => true
  | OnlyIfNecessary => false
  | ParoundName => grav_name pgrav <> fname
  | ParoundPrec => grav_prec pgrav <> fprec

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

fun grule_term_names G grule = let
  fun suffix rr = (#term_name rr, (#timestamp rr, SUFFIX (STD_suffix [rr])))
  fun prefix rr = (#term_name rr, (#timestamp rr, PREFIX (STD_prefix [rr])))
  fun mkifix a rr = (#term_name rr,
                     (#timestamp rr, INFIX (STD_infix ([rr], a))))
  fun closefix rr = (#term_name rr, (#timestamp rr, CLOSEFIX [rr]))
  fun bstamp LAMBDA = 0
    | bstamp (BinderString r) = #timestamp r
in
  case grule of
    PREFIX (STD_prefix list) => map prefix list
  | PREFIX (BINDER list) =>
      map (fn b => (binder_to_string G b, (bstamp b, PREFIX (BINDER [b])))) list
      (* binder_to_string is incomplete on LAMBDA, but this doesn't matter
         here as the information generated here is not used to print
         pure LAMBDAs *)
  | SUFFIX (STD_suffix list) => map suffix list
  | SUFFIX TYPE_annotation => []
  | INFIX (STD_infix(list, a)) => map (mkifix a) list
  | INFIX RESQUAN_OP => [(resquan_special, (0, grule))]
  | INFIX (FNAPP lst) =>
      (fnapp_special, (0, INFIX (FNAPP []))) :: map (mkifix LEFT) lst
  | INFIX VSCONS => [(vs_cons_special, (0, INFIX VSCONS))]
  | CLOSEFIX lst => map closefix lst
  | LISTRULE lspeclist => let
      fun process lspec = [(#cons lspec, (0, LISTRULE [lspec])),
                           (#nilstr lspec, (0, LISTRULE [lspec]))]
    in
      List.concat (map process lspeclist)
    end
end

exception DoneExit

(* fun symbolic s = List.all HOLsym (String.explode s) *)

fun symbolic s = HOLsym (String.sub(s,String.size(s)-1));

fun unfakeconst vnm =
    case Lib.total (Lib.unprefix GrammarSpecials.fakeconst_special) vnm of
      SOME s => SOME("", s)
        (* first argument in result might conceivably contain useful
           information, but I'm not sure what it should be right now *)
   | NONE => NONE

fun grammar_name G tm = let
  val oinfo = term_grammar.overload_info G
in
  if is_const tm then
    Overload.overloading_of_term oinfo tm
  else if is_var tm then let
      val (vnm, _) = dest_var tm
    in
      case unfakeconst vnm of
        NONE => SOME vnm
      | SOME(_ (* thy *), nm) => SOME nm
    end
  else NONE
end

(* term tm can be seen to have name s according to grammar G *)
fun has_name G s tm = (grammar_name G tm = SOME s)

(* term tm might be the product of parsing name s -
   weaker than has_name *)
fun has_name_by_parser G s tm = let
  val oinfo = term_grammar.overload_info G
in
  case Overload.info_for_name oinfo s of
    NONE => false
  | SOME {actual_ops,...} =>
    List.exists (fn t => can (match_term t) tm) actual_ops
end

datatype bvar
    = Simple of term
    | Restricted of {Bvar : term, Restrictor : term}

fun bv2term (Simple t) = t
  | bv2term (Restricted {Bvar,...}) = Bvar



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

val prettyprint_bigrecs = ref true;

val _ = register_btrace ("pp_bigrecs", prettyprint_bigrecs)

fun first_tok [] = raise Fail "Shouldn't happen term_pp 133"
  | first_tok (RE (TOK s)::_) = s
  | first_tok (_ :: t) = first_tok t

fun decdepth n = if n < 0 then n else n - 1

fun atom_name tm = let
  val (vnm, _) = dest_var tm
in
  case unfakeconst vnm of
    NONE => vnm
  | SOME((* thy *)_, nm) => nm
end handle HOL_ERR _ => fst (dest_const tm)


fun pp_term (G : grammar) TyG backend = let
  fun block x = backend_block backend x
  fun tystr ty =
      PP.pp_to_string 10000 (type_pp.pp_type TyG PPBackEnd.raw_terminal) ty
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
      SOME [(_, _, LISTRULE[{separator, leftdelim, rightdelim,...}])] =>
        SOME (leftdelim, rightdelim, separator)
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
  val printers_exist = Net.size uprinters > 0

  (* This code will print paired abstractions "properly" only if
        1. the term has a constant in the right place, and
        2. that constant maps to the name "UNCURRY" in the overloading map.
     These conditions are checked in the call to grammar_name.

     We might vary this.  In particular, in 2., we could check to see
     name "UNCURRY" maps to a term (looking at the overload map in the
     reverse direction).

     Another option again might be to look to see if the term is a
     constant whose real name is UNCURRY, and if this term also maps
     to the name UNCURRY.  This last used to be the actual
     implementation, but it's hard to do this in the changed world
     (since r6355) of "syntactic patterns" because of the way
     overloading resolution can create fake constants (concealing true
     names) before this code gets a chance to run.

     The particular choice made above means that the printer does the
     'right thing'
       (prints `(\(x,y). x /\ y)` as `pair$UNCURRY (\x y. x /\ y)`)
     if given a paired abstraction to print wrt an "earlier" grammar,
     such boolTheory.bool_grammars. *)

  fun my_dest_abs tm =
      case dest_term tm of
        LAMB p => p
      | COMB(Rator,Rand) => let
          val _ =
              grammar_name G Rator = SOME "UNCURRY" orelse
              raise PP_ERR "my_dest_abs" "term not an abstraction"
          val (v1, body0) = my_dest_abs Rand
          val (v2, body) = my_dest_abs body0
        in
          (mk_pair(v1, v2), body)
        end
      | _ => raise PP_ERR "my_dest_abs" "term not an abstraction"

  fun my_is_abs tm = can my_dest_abs tm
  fun my_strip_abs tm = let
    fun recurse acc t = let
      val (v, body) = my_dest_abs t
    in
      recurse (v::acc) body
    end handle HOL_ERR _ => (List.rev acc, t)
  in
    recurse [] tm
  end

  (* allow any constant that overloads to the string "LET" to be treated as
     a let. *)
  fun is_let0 n tm = let
    val (let_tm,f_tm) = dest_comb(rator tm)
  in
    grammar_name G let_tm = SOME "LET" andalso
    (length (#1 (my_strip_abs f_tm)) >= n orelse is_let0 (n + 1) f_tm)
  end handle HOL_ERR _ => false
  val is_let = is_let0 1



  fun dest_vstruct bnder res t =
      case bnder of
        NONE => let
        in
          case (Lib.total my_dest_abs t, res) of
            (SOME (bv, body), _) => (Simple bv, body)
          | (NONE, NONE) =>
               raise PP_ERR "dest_vstruct" "term not an abstraction"
          | (NONE, SOME s) => let
            in
              case dest_term t of
                COMB (Rator, Rand) => let
                in
                  case dest_term Rator of
                    COMB(rator1, rand1) =>
                    if has_name G s rator1 andalso my_is_abs Rand then let
                        val (bv, body) = my_dest_abs Rand
                      in
                        (Restricted{Bvar = bv, Restrictor = rand1}, body)
                      end
                    else raise PP_ERR "dest_vstruct" "term not an abstraction"
                  | _ => raise PP_ERR "dest_vstruct" "term not an abstraction"
                end
              | _ => raise PP_ERR "dest_vstruct" "term not an abstraction"
            end
        end
      | SOME s => let
        in
          case (dest_term t) of
            COMB(Rator,Rand) => let
            in
              if has_name G s Rator andalso my_is_abs Rand then let
                  val (bv, body) = my_dest_abs Rand
                in
                  (Simple bv, body)
                end
              else
                case res of
                  NONE => raise PP_ERR "dest_vstruct" "term not an abstraction"
                | SOME s => let
                  in
                    case (dest_term Rator) of
                      COMB(rator1, rand1) =>
                      if has_name G s rator1 andalso my_is_abs Rand then let
                          val (bv, body) = my_dest_abs Rand
                        in
                            (Restricted{Bvar = bv, Restrictor = rand1}, body)
                        end
                      else
                        raise PP_ERR "dest_vstruct" "term not an abstraction"
                    | _ =>
                      raise PP_ERR "dest_vstruct" "term not an abstraction"
                  end
            end
          | _ => raise PP_ERR "dest_vstruct" "term not an abstraction"
        end


  fun strip_vstructs bnder res tm = let
    fun strip acc t = let
      val (bvar, body) = dest_vstruct bnder res t
    in
      strip (bvar::acc) body
    end handle HOL_ERR _ => (List.rev acc, t)
  in
    strip [] tm
  end

  fun strip_nvstructs bnder res n tm = let
    fun strip n acc tm =
        if n <= 0 then (List.rev acc, tm)
        else let
            val (bvar, body) = dest_vstruct bnder res tm
          in
            strip (n - 1) (bvar :: acc) body
          end
  in
    strip n [] tm
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
     if printers_exist then let
         fun sysprint (pg,lg,rg) depth tm = pr_term tm pg lg rg depth
         val candidates = Net.match tm uprinters
         fun test (pat,_,_) = can (match_term pat) tm
         fun printwith f = f (TyG, G)
                             backend sysprint ppfns
                             (pgrav, lgrav, rgrav)
                             depth tm
            fun runfirst [] = pr0 tm
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
    fun add_ann_string (s,ann) = add_xstring {s=s,ann=SOME ann,sz=NONE}
    fun block_by_style (addparens, rr, pgrav, fname, fprec) = let
      val needed =
        case #1 (#block_style (rr:rule_record)) of
          AroundSameName => grav_name pgrav <> fname
        | AroundSamePrec => grav_prec pgrav <> fprec
        | AroundEachPhrase => true
        | NoPhrasing => false
      val bblock = uncurry block (#2 (#block_style rr))
    in
      if needed orelse addparens then bblock else I
    end
    fun pbegin b = if b then add_string "(" else nothing
    fun pend b = if b then add_string ")" else nothing
    fun spacep b = if b then add_break(1, 0) else nothing
    fun hardspace n = add_string (string_of_nspaces n)
    fun sizedbreak n = add_break(n, 0)

    fun doTy ty =
        liftpp (fn pps =>
                   type_pp.pp_type_with_depth TyG backend pps (decdepth depth)
                   ty)

    (* els is a list of pp_elements; args is a list of terms to be inserted
       in place of RE TM elements.  Returns the unused args *)
    fun print_ellist (lprec, cprec, rprec) (els, args : term list) = let
      val recurse  = print_ellist (lprec, cprec, rprec)
    in
      case els of
        [] => return args
      | (e :: es) => let
        in
          case e of
            PPBlock(more_els, (sty, ind)) =>
              block sty ind (recurse (more_els,args)) >-
              (fn rest => recurse (es,rest))
          | HardSpace n => (hardspace n >> recurse (es, args))
          | BreakSpace (n, m) => (add_break(n,m) >> recurse (es, args))
          | RE (TOK s) => (add_string s >> recurse (es, args))
          | RE TM => (pr_term (hd args) Top Top Top (decdepth depth) >>
                      recurse (es, tl args))
          | FirstTM => (pr_term (hd args) cprec lprec cprec (decdepth depth) >>
                        recurse (es, tl args))
          | LastTM => (pr_term (hd args) cprec cprec rprec (decdepth depth) >>
                       recurse (es, tl args))
          | EndInitialBlock _ => raise Fail "term_pp - encountered EIB"
          | BeginFinalBlock _ => raise Fail "term_pp - encountered BFB"
        end
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
            pr_t tm Top Top Top (decdepth depth)
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
        case Overload.overloading_of_term overload_info tm of
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


    fun pr_res_vstructl restrictor res_op vsl = let
      val simples = map (Simple o bv2term) vsl
      val add_final_parens = restrictor might_print endbinding
    in
      block CONSISTENT 2
        (block INCONSISTENT 2
           (pr_list pr_vstruct (add_break(1,0)) simples) >>
         add_string res_op >>
         pbegin add_final_parens >>
         pr_term restrictor Top Top Top (decdepth depth) >>
         pend add_final_parens)
    end
    fun can_print_vstructl vsl = let
      fun recurse acc [] = SOME acc
        | recurse acc ((Simple _)::_) = NONE
        | recurse acc (Restricted{Restrictor = t,...}::xs) = let
          in
            if t = acc then recurse acc xs else NONE
          end
    in
      case vsl of
        [] => raise PP_ERR "can_print_vstructl" "Empty list!"
      | (Simple _::xs) => NONE
      | (Restricted{Restrictor = t,...}::xs) => recurse t xs
    end

    (* the pr_vstructl function figures out which way to print a given
       list of vstructs *)
    fun pr_vstructl vsl =
      case can_print_vstructl vsl of
        SOME r => pr_res_vstructl r res_quanop vsl
      | _ => let
        in
          block INCONSISTENT 2
                (pr_list pr_vstruct (add_break(1,0)) vsl)
        end

    fun pr_abs tm = let
      val addparens = lgrav <> RealTop orelse rgrav <> RealTop
      val restr_binder =
          find_partial (fn (b,s) => if b = NONE then SOME s else NONE)
                       restr_binders
      val (bvars, body) = strip_vstructs NONE restr_binder tm
      val bvars_seen_here = List.concat (map (free_vars o bv2term) bvars)
    in
      pbegin addparens >>
      block CONSISTENT 2
            (add_string (hd lambda) >>
             record_bvars bvars_seen_here
               (pr_vstructl bvars >>
                add_string endbinding >> add_break (1,0) >>
                pr_term body Top Top Top (decdepth depth))) >>
      pend addparens
    end

    fun is_fakeconst tm = let
      val (vnm, _) = dest_var tm
    in
      String.isPrefix GrammarSpecials.fakeconst_special vnm
    end handle HOL_ERR _ => false
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
          | SOME oi => mem inj_t (#actual_ops oi)
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
      pbegin showtypes >>
      add_string (numeral_str ^ sfx) >>
      (if showtypes then
         add_string (" "^type_intro) >> add_break (0,0) >>
         doTy (#2 (dom_rng injty))
       else nothing) >>
      pend showtypes
    end

    exception NotReallyARecord

    fun check_for_field_selection t1 t2 = let
      fun getfldname s =
          if isSome recsel_info then
            if isPrefix recsel_special s then
              SOME (String.extract(s, size recsel_special, NONE), t2)
            else if is_substring bigrec_subdivider_string s andalso
                    !prettyprint_bigrecs
            then let
                open Overload
                val brss = bigrec_subdivider_string
                val (f, x) = dest_comb t2
                val _ = is_const f orelse raise NotReallyARecord
                val fname = valOf (overloading_of_term overload_info f)
                val _ = is_substring (brss ^ "sf") fname orelse
                        raise NotReallyARecord
                open Substring
                val (_, brsssguff) = position brss (full s)
                val dropguff = slice(brsssguff, String.size brss, NONE)
                val dropdigits = dropl Char.isDigit dropguff
                val fldname = string(slice(dropdigits, 1, NONE))
              in
                SOME (fldname, x)
              end handle HOL_ERR _ => NONE
                       | NotReallyARecord => NONE
                       | Option => NONE
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
              in
                block INCONSISTENT 0
                      (pbegin add_parens >>
                       pr_term t2 prec lprec prec (decdepth depth) >>
                       add_string fldtok >>
                       add_break(0,0) >>
                       add_string fldname >>
                       pend add_parens)
              end
            | NONE => fail
          end
        | NONE => fail
      else fail
    end

    fun check_for_record_update t1 t2 =
        if isSome recwith_info andalso isSome reclist_info andalso
           isSome recfupd_info andalso isSome recupd_info
        then let
            open Overload
            (* function to determine if t is a record update *)
            fun is_record_update t =
                if is_comb t andalso is_const (rator t) then let
                    val rname = overloading_of_term overload_info (rator t)
                  in
                    case rname of
                      SOME s =>
                      (!prettyprint_bigrecs andalso isSuffix "_fupd" s andalso
                       is_substring (bigrec_subdivider_string ^ "sf") s) orelse
                      isPrefix recfupd_special s
                    | NONE => false
                  end else false
            (* descend the rands of a term until one that is not a record
               update is found.  Return this and the list of rators up to
               this point. *)
            fun find_first_non_update acc t =
                if is_comb t andalso is_record_update (rator t) then
                  find_first_non_update ((rator t)::acc) (rand t)
                else
                  (List.rev acc, t)
            fun categorise_bigrec_updates v = let
              fun bigrec_update t =
                  if is_comb t then
                    case overloading_of_term overload_info (rator t) of
                      SOME s => if is_substring bigrec_subdivider_string s then
                                  SOME (s, rand t)
                                else NONE
                    | NONE => NONE
                  else NONE
              fun strip_o acc tlist =
                  case tlist of
                    [] => acc
                  | t::ts => let
                      val (f, args) = strip_comb t
                      val {Name,Thy,...} = dest_thy_const f
                    in
                      if Name = "o" andalso Thy = "combin" then
                        strip_o acc (hd (tl args) :: hd args :: ts)
                      else strip_o (t::acc) ts
                    end handle HOL_ERR _ => strip_o (t::acc) ts
              fun strip_bigrec_updates t = let
                val internal_upds = strip_o [] [t]
              in
                List.mapPartial bigrec_update internal_upds
              end
            fun categorise_bigrec_update (s, value) = let
              (* first strip suffix, and decide if a normal update *)
              val sz = size s
              val (s, value, value_upd) = let
                (* suffix will be "_fupd" *)
                val (f, x) = dest_comb value
                val {Thy, Name, ...} = dest_thy_const f
              in
                if Thy = "combin" andalso Name = "K" then
                  (String.extract(s, 0, SOME (sz - 5)), x, true)
                else
                  (String.extract(s, 0, SOME (sz - 5)), value, false)
              end handle HOL_ERR _ =>
                         (String.extract(s,0,SOME (sz - 5)), value, false)

              val ss = Substring.full s
              val (_, ss) = (* drop initial typename *)
                  Substring.position bigrec_subdivider_string ss
              val ss = (* drop bigrec_subdivider_string *)
                  Substring.slice(ss, size bigrec_subdivider_string, NONE)
              val ss = (* drop subrecord number *)
                  Substring.dropl Char.isDigit ss
              val ss = (* drop underscore before field name *)
                  Substring.slice(ss, 1, NONE)
            in
              (Substring.string ss, value, value_upd)
            end handle Subscript => raise NotReallyARecord
          in
            map categorise_bigrec_update (strip_bigrec_updates v)
          end
          fun categorise_update t = let
            (* t is an update, possibly a bigrec monster.  Here we generate
               a list of real updates (i.e., the terms corresponding to the
               new value in the update), each with an accompanying field
               string, and a boolean, which is true iff the update is a value
               update (not a "fupd") *)
            val (fld, value) = dest_comb t
            val rname = valOf (Overload.overloading_of_term overload_info fld)
          in
            if isPrefix recfupd_special rname then let
                val (f, x) = dest_comb value
                val {Thy, Name,...} = dest_thy_const f
                val fldname = String.extract(rname,size recfupd_special, NONE)
              in
                if Thy = "combin" andalso Name = "K" then [(fldname, x, true)]
                else [(fldname, value, false)]
              end handle HOL_ERR _ =>
                         [(String.extract(rname,size recfupd_special, NONE),
                           value, false)]
            else (* is a big record - examine value *)
              assert (not o null) (categorise_bigrec_updates value)
              handle HOL_ERR _ => raise NotReallyARecord
          end
        in
          if is_record_update t1 then let
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
                    (add_string fld >>
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
                                print_ellist(Top,Top,Top) (sep, []) >>
                                recurse (decdepth depth) us)
            in
              print_ellist (Top,Top,Top) (ldelim, []) >>
              block INCONSISTENT 0 (recurse depth updates) >>
              print_ellist (Top,Top,Top) (rdelim, []) >>
              nothing
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
              pbegin addparens >>
              block INCONSISTENT 0
                    (pr_term base with_grav lprec with_grav (decdepth depth) >>
                     add_string " " >>
                     add_string with_tok >>
                     add_break (1,0) >>
                     (if length updates = 1 then print_update depth (hd updates)
                      else print_updlist updates)) >>
              pend addparens
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
          case Overload.overloading_of_term overload_info f of
            NONE => let
              val {Thy,Name,Ty} = dest_thy_const f
            in
              type_of (prim_mk_const {Thy = Thy, Name = Name})
            end
          | SOME print_name =>
            #base_type
              (valOf (Overload.info_for_name overload_info print_name))
      end
      val base_pty = Pretype.rename_typevars [] (Pretype.fromType base_ty)
      fun foldthis (tm,acc) = let
        open Pretype
        val fn_pty = mk_fun_ty(fromType (type_of tm), new_uvar())
      in
        unify acc fn_pty; chase acc
      end
      val _ = List.foldl foldthis base_pty args
    in
      Pretype.has_unbound_uvar base_pty
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
      pbegin (addparens orelse comb_show_type) >>
      block INCONSISTENT 2
            (full_pr_term binderp showtypes showtypes_v ppfns RatorCP t1
                          prec lprec prec (decdepth depth) >>
             add_break (1, 0) >>
             full_pr_term binderp showtypes showtypes_v ppfns RandCP t2
                          prec prec rprec (decdepth depth) >>
             (if comb_show_type then
                (add_string (" "^type_intro) >> add_break (0,0) >>
                 liftpp (fn pps =>
                            type_pp.pp_type_with_depth TyG backend pps
                                                       (decdepth depth)
                                                       (type_of tm)))
              else nothing)) >>
      pend (addparens orelse comb_show_type)
    end

    fun pr_sole_name tm n rules = let
      (* This function prints a solitary name n.  The rules are possibly
         relevant rules from the grammar.  If one is a list rule, and our
         n is the name of the nil case, then we should print that
         list's delimiters around nothing.
         Otherwise, the presence of a rule with our name n in it, is a
         probable indication that our name will need a $ printed out in
         front of it. *)
      fun check_rule rule =
        case rule of
          LISTRULE lrules => List.find (fn r => #nilstr r = n) lrules
        | _ => NONE
      val nilrule = find_partial check_rule rules
      val fakerec = {Thy = "", Name = "", Ty = Type.alpha}
      val ty = type_of tm
      fun add s = let
        fun addk bvs =
          if is_const tm then
            add_ann_string (s, PPBackEnd.Const (dest_thy_const tm, s))
          else if is_fakeconst tm then
            add_ann_string (s, PPBackEnd.Const (fakerec, s))
          else if HOLset.member(bvs,tm) orelse binderp then
            add_ann_string (s, PPBackEnd.BV (ty, fn () => tystr ty))
          else
            add_ann_string (s, PPBackEnd.FV (ty, fn () => tystr ty))
      in
        getbvs >- addk
      end
    in
      case nilrule of
        SOME r => print_ellist (Top,Top,Top) (#leftdelim r, []) >>
                  print_ellist (Top,Top,Top) (#rightdelim r, []) >>
                  return ()
      | NONE => let
          (* if only rule is a list form rule and we've got to here, it
             will be a rule allowing this to the cons part of a list form.
             Such functions don't need to be dollar-ed *)
        in
          case rules of
            [LISTRULE _] => add n
          | _ =>
              if HOLset.member(spec_table, n) then dollarise add add_string n
              else add n
        end
    end


    fun pr_comb_with_rule frule fterm args Rand = let
      val {fname,fprec,f} = fterm
      val comb_show_type = comb_show_type(f,args @ [Rand])
      val ptype_block =
          if comb_show_type then
            fn p =>
               add_string "(" >>
               block CONSISTENT 0
                  (p >> add_break (1,2) >>
                   add_string type_intro >>
                   doTy (type_of tm)) >>
               add_string ")"
          else fn p => p
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
          val begblock = block_by_style(addparens, rr, pgrav, fname, fprec)
        in
          ptype_block
              (pbegin (addparens orelse comb_show_type) >>
               begblock
                    (print_ellist (lprec, prec, rprec)
                                  (pp_elements, arg_terms)) >>
               pend (addparens orelse comb_show_type))
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
            block_by_style(addparens, rr, pgrav, fname, fprec)
        in
          ptype_block
              (pbegin (addparens orelse comb_show_type) >>
               begblock
                 (print_ellist (lprec, prec, Top) (pp_elements, real_args)) >>
               pend (addparens orelse comb_show_type))
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
              combpos = RandCP
          val rprec = if addparens then Top else rgrav
          val pp_elements = block_up_els [] (elements @ [LastTM])
          val real_args = args @ [Rand]
          val prec = Prec(fprec, fname)
          val begblock = block_by_style(addparens, rr, pgrav, fname, fprec)
        in
          ptype_block
              (pbegin (addparens orelse comb_show_type) >>
               begblock
                 (print_ellist (Top, prec, rprec) (pp_elements, real_args)) >>
               pend (addparens orelse comb_show_type))
        end
      | PREFIX (BINDER lst) => let
          val tok = case hd lst of
                      LAMBDA => hd lambda (* should never happen *)
                    | BinderString r => #tok r
          fun find (bopt, s) = if bopt = SOME fname then SOME s else NONE
          val restr_binder = find_partial find restr_binders
          val (bvs, body) = strip_vstructs (SOME fname) restr_binder tm
          val bvars_seen_here = List.concat (map (free_vars o bv2term) bvs)
          val addparens =
            case rgrav of
              Prec(n, _) => n > fprec
            | _ => false
          val addparens = addparens orelse combpos = RandCP
        in
          ptype_block
            (pbegin (addparens orelse comb_show_type) >>
             block INCONSISTENT 2
               (add_string tok >>
                record_bvars bvars_seen_here
                  (pr_vstructl bvs >>
                   add_string endbinding >> spacep true >>
                   block CONSISTENT 0
                     (pr_term body Top Top Top (decdepth depth)))) >>
             pend (addparens orelse comb_show_type))
        end
      | CLOSEFIX lst => let
          val rr = hd lst
          val elements = #elements rr
        in
          ptype_block
            (uncurry block (#2 (#block_style rr))
               (print_ellist (Top, Top, Top) (elements, args @ [Rand]) >>
                return ()))
        end
      | LISTRULE lrules => let
          val (r as {nilstr, cons, block_info,...}) =
            valOf (List.find (fn r => #cons r = fname) lrules)
          val sep = #separator r
          val rdelim = #rightdelim r
          val ldelim = #leftdelim r
          val (consistency, breakspacing) = block_info
          (* list will never be empty *)
          fun pr_list tm = let
            fun recurse depth tm = let
              val (_, args) = strip_comb tm
              val head = hd args
              val tail = List.nth(args, 1)
            in
              if depth = 0 then add_string "..."
              else if has_name_by_parser G nilstr tail then
                (* last element *)
                pr_term head Top Top Top (decdepth depth)
              else let
              in
                pr_term head Top Top Top (decdepth depth) >>
                print_ellist (Top,Top,Top) (sep, []) >>
                recurse (decdepth depth) tail
              end
            end
          in
            print_ellist (Top,Top,Top) (ldelim, []) >>
            block consistency breakspacing (recurse depth tm) >>
            print_ellist (Top,Top,Top) (rdelim, []) >> return ()
          end
        in
          ptype_block (pr_list tm)
        end
    end

    fun pr_let0 tm = let
      fun find_base acc tm =
        if is_let tm then let
          val (let_tm, args) = strip_comb tm
        in
          find_base (List.nth(args, 1)::acc) (hd args)
        end
        else (acc, tm)
      fun pr_leteq (bv, tm2) = let
        val (args, rhs_t) = strip_vstructs NONE NONE tm2
        val fnarg_bvars = List.concat (map (free_vars o bv2term) args)
        val bvfvs = free_vars (bv2term bv)
      in
        block INCONSISTENT 2
              (record_bvars bvfvs (pr_vstruct bv) >>
               spacep true >>
               record_bvars fnarg_bvars
                  (pr_list pr_vstruct (spacep true) args >>
                   spacep (not (null args)) >>
                   add_string "=" >> spacep true >>
                   block INCONSISTENT 2
                     (pr_term rhs_t Top Top Top (decdepth depth)))) >>
        return bvfvs
      end
      val (values, abstr) = find_base [] tm
      val (varnames, body) =
          strip_nvstructs NONE NONE (length values) abstr
      val name_value_pairs = ListPair.zip (varnames, values)
      val bodyletp = is_let body
      fun record_bvars new =
          (* overriding term_pp_utils's version; this one has a different type also *)
          getbvs >- (fn old => setbvs (HOLset.addList(old,new)))
    in
      (* put a block around the "let ... in" phrase *)
      block CONSISTENT 0
            (add_string "let" >> add_string " " >>
             (* put a block around the variable bindings *)
             block INCONSISTENT 0
               (mappr_list pr_leteq (add_string " " >> add_string "and" >>
                                     spacep true)
                           name_value_pairs >-
                (return o List.concat)) >-
             record_bvars >>
             (if bodyletp then (spacep true >> add_string "in")
              else nothing)) >>
     spacep true >>
     (if bodyletp then pr_let0 body
      else add_string "in" >> add_break(1,2) >>
           pr_term body RealTop RealTop RealTop (decdepth depth))
    end

    fun pr_let lgrav rgrav tm = let
      val addparens = lgrav <> RealTop orelse rgrav <> RealTop
    in
      getbvs >- (fn oldbvs =>
      pbegin addparens >>
      block CONSISTENT 0 (pr_let0 tm) >>
      pend addparens >>
      setbvs oldbvs)
    end

    fun print_ty_antiq tm = let
      val ty = parse_type.dest_ty_antiq tm
    in
      block CONSISTENT 2
            (add_string "(ty_antiq(" >>
             add_break(0,0) >>
             add_string "`:" >>
             liftpp (fn pps =>
                        type_pp.pp_type_with_depth TyG backend pps
                                                   (decdepth depth) ty) >>
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
      case Overload.overloading_of_term overload_info tm of
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
              (true, #2 (valOf (unfakeconst vname)))
              handle Option => (false, vname)
          val vrule = lookup_term vname
          val add_type=
            add_string (" "^type_intro) >>  add_break(0,0) >> doTy Ty
          fun new_freevar ({seen_frees,current_bvars,...}:printing_info) =
            showtypes andalso not isfake andalso
            not (HOLset.member(seen_frees, tm)) andalso
            not (HOLset.member(current_bvars, tm)) andalso not binderp
          fun calc_print_type nfv =
            showtypes_v orelse
            showtypes andalso not isfake andalso (binderp orelse nfv)
          fun adds s =
              getbvs >- (fn bvs =>
              if HOLset.member(bvs, tm) orelse binderp then
                add_ann_string (s, PPBackEnd.BV (Ty, fn () => s^": "^tystr Ty))
              else if not isfake then
                add_ann_string (s, PPBackEnd.FV (Ty, fn () => s^": "^tystr Ty))
              else add_ann_string(s, PPBackEnd.Const({Ty = Ty, Thy = "??",
                                                      Name = "??"}, s)))
        in
          fupdate (fn x => x) >- return o new_freevar >-
          (fn is_new =>
              (if is_new then spotfv tm else nothing) >>
              return (calc_print_type is_new) >-
          (fn print_type =>
          block INCONSISTENT 2
                (pbegin print_type >>
                 (if isSome vrule then
                    pr_sole_name tm vname (map #3 (valOf vrule))
                  else
                    if HOLset.member(spec_table, vname) then
                      dollarise adds add_string vname
                    else adds vname) >>
                 (if print_type then add_type else nothing) >>
                 pend print_type)))
        end
      | CONST(c as {Name, Thy, Ty}) => let
          val add_ann_string = fn s => add_ann_string (s, PPBackEnd.Const (c,s))
          fun add_prim_name() = add_ann_string (Thy ^ "$" ^ Name)
          fun with_type action = let
          in
            pbegin true >>
            action() >> add_string (" "^type_intro) >> doTy Ty >>
            pend true
          end
          val r = {Name = Name, Thy = Thy}
          fun normal_const () = let
            fun cope_with_rules s = let
              val crules = lookup_term s
            in
              if isSome crules then
                pr_sole_name tm s (map #3 (valOf crules))
              else if s = "0" andalso can_pr_numeral NONE then
                pr_numeral NONE tm
              else if Literal.is_emptystring tm then
                add_string "\"\""
              else add_ann_string s
            end
          in
            if Name = "the_value" andalso Thy = "bool" then let
                val {Args,...} = dest_thy_type Ty
              in (* TODO: annotate all of this as the constant somehow *)
                add_string "(" >>
                block CONSISTENT 0 (add_string type_intro >> doTy (hd Args)) >>
                add_string ")"
              end
            else
              case Overload.overloading_of_term overload_info tm of
                NONE => add_prim_name()
              | SOME s =>
                (* term is overloaded *)
                if isPrefix recsel_special s orelse
                   isPrefix recupd_special s orelse
                   isPrefix recfupd_special s
                then
                  (* if overloaded to a record special, check to see if it *)
                  (* has a normal name in the map that we could use instead. *)
                  (* This way we will print out something that can still be *)
                  (* parsed back to the original term, without having to go *)
                  (* for full uglification with dollared syntax.  *)

                  (* Note that if we've got this far, we can't print out *)
                  (* the special record syntax for some other reason, so *)
                  (* is our "fall-back" action *)
                  case Overload.info_for_name overload_info Name of
                    NONE => add_prim_name()
                  | SOME {actual_ops,...} =>
                    if List.exists (aconv tm) actual_ops then
                      cope_with_rules Name
                    else
                      add_prim_name()
                else if s = "case" then
                  cope_with_rules Name
                else
                  cope_with_rules s
          end
        in
          case (showtypes_v, const_is_polymorphic tm, const_has_multi_ovl tm) of
            (true, false, true) => add_prim_name()
          | (true, true, true) => with_type add_prim_name
          | (true, true, false) => with_type normal_const
          | _ => if !show_types andalso combpos <> RatorCP andalso
                    const_is_polymorphic tm
                 then
                   with_type normal_const
                 else normal_const()
        end
      | COMB(Rator, Rand) => let
          val (f, args) = strip_comb Rator
          val (oif, oiargs) =
              case Overload.oi_strip_comb overload_info tm of
                NONE => (f, args @ [Rand])
              | SOME p => p

          fun check_for_setcomprehensions () =
              if grammar_name G oif = SOME "GSPEC" andalso my_is_abs Rand
              then let
                  val (vs, body) = my_dest_abs Rand
                  val vfrees = FVL [vs] empty_tmset
                  val bvars_seen_here = HOLset.listItems vfrees

                  val (l, r) = dest_pair body
                  val lfrees = FVL [l] empty_tmset
                  val rfrees = FVL [r] empty_tmset
                  open HOLset
                in
                  if (equal(intersection(lfrees,rfrees), vfrees) orelse
                      (isEmpty lfrees andalso equal(rfrees, vfrees)) orelse
                      (isEmpty rfrees andalso equal(lfrees, vfrees)))
                     andalso not (!unamb_comp)
                  then
                    block CONSISTENT 0
                       (record_bvars bvars_seen_here
                        (set_gspec
                           (add_string "{" >>
                            block CONSISTENT 0
                              (pr_term l Top Top Top (decdepth depth) >>
                               hardspace 1 >> add_string "|" >> spacep true >>
                               pr_term r Top Top Top (decdepth depth)) >>
                            add_string "}")))
                  else
                    block CONSISTENT 0
                      (record_bvars bvars_seen_here
                       (set_gspec
                         (add_string "{" >>
                          block CONSISTENT 0
                            (pr_term l Top Top Top (decdepth depth) >>
                             hardspace 1 >> add_string "|" >> spacep true >>
                             pr_term vs Top Top Top (decdepth depth) >>
                             hardspace 1 >> add_string "|" >> spacep true >>
                             pr_term r Top Top Top (decdepth depth)) >>
                          add_string "}")))
                end handle HOL_ERR _ => fail
              else fail



          fun is_atom tm = is_const tm orelse is_var tm
          fun pr_atomf (f,args) = let
            (* the tm, Rator and Rand bindings that we began with are
               overridden by the f and args values that may be the product of
               oi_strip_comb *)
            val fname = atom_name f
            val tm = list_mk_comb (f, args)
            val Rator = rator tm
            val (args,Rand) = front_last args
            val candidate_rules = lookup_term fname
            fun is_list (r as {nilstr, cons, ...}:listspec) tm =
                has_name_by_parser G nilstr tm orelse
                (is_comb tm andalso
                 let
                   val (t0, tail) = dest_comb tm
                 in
                   is_list r tail andalso is_comb t0 andalso
                   has_name G cons (rator t0)
                 end)
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
                    val optrule = lookup_term bindex
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
              if is_let tm then pr_let lgrav rgrav tm
              else let
                in
                  case restr_binder of
                    NONE => pr_comb tm Rator Rand
                  | SOME NONE =>
                    if isSome restr_binder_rule then pr_abs tm
                    else pr_comb tm Rator Rand
                  | SOME (SOME fname) =>
                    if isSome restr_binder_rule then
                      pr_comb_with_rule(#3(valOf restr_binder_rule))
                                       {fprec = #1 (valOf restr_binder_rule),
                                        fname = fname,
                                        f = f} args Rand
                    else
                      pr_comb tm Rator Rand
                end
            | SOME crules0 => let
                fun suitable_rule rule =
                    case rule of
                      INFIX(STD_infix(rrlist, _)) =>
                      numTMs (rule_elements (#elements (hd rrlist))) + 1 =
                      length args
                    | INFIX RESQUAN_OP => raise Fail "Can't happen 90212"
                    | PREFIX (STD_prefix list) =>
                      numTMs (rule_elements (#elements (hd list))) =
                      length args
                    | PREFIX (BINDER _) => my_is_abs Rand andalso
                                           length args = 0
                    | SUFFIX (STD_suffix list) =>
                      numTMs (rule_elements (#elements (hd list))) =
                      length args
                    | SUFFIX Type_annotation => raise Fail "Can't happen 90210"
                    | CLOSEFIX list =>
                      numTMs (rule_elements (#elements (hd list))) - 1 =
                      length args
                    | INFIX (FNAPP _) => raise Fail "Can't happen 90211"
                    | INFIX VSCONS => raise Fail "Can't happen 90213"
                    | LISTRULE list => is_list (hd list) tm
                val crules = List.filter (suitable_rule o #3) crules0
                fun is_lrule (LISTRULE _) = true | is_lrule _ = false
                val first_nonlist = List.find (not o is_lrule o #3) crules
                val lrules = List.filter (is_lrule o #3) crules
              in
                case (lrules, first_nonlist) of
                  ((prec,_,rule) :: _, _) =>
                    pr_comb_with_rule rule {fprec = prec, fname=fname, f=f} args Rand
                | ([], SOME (p, _, r)) =>
                    pr_comb_with_rule r {fprec=p, fname=fname, f=f} args Rand
                | ([], NONE) => pr_comb tm Rator Rand
              end
          end (* pr_atomf *)
          fun maybe_pr_atomf () =
              if grammar_name G f = SOME "case" then
                pr_atomf (strip_comb tm)
              else
                case Overload.oi_strip_comb overload_info tm of
                  SOME (p as (f,args)) => let
                  in
                    case args of
                      [] => pr_term f pgrav lgrav rgrav depth
                    | _ => pr_atomf p
                  end
                | NONE => if is_var f then pr_atomf (f, args @ [Rand])
                          else pr_comb tm Rator Rand
        in
          (* check for various literal and special forms *)

          (* strings *)
          (case total Literal.dest_string_lit tm of
             NONE => fail
           | SOME s => add_string (Literal.string_literalpp s)) |||

          (* characters *)
          (fn _ => case total Literal.dest_char_lit tm of
             NONE => fail
           | SOME c => add_string ("#" ^ Lib.mlquote (str c))) |||

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
          (fn _ => check_for_record_update Rator Rand) |||

          check_for_setcomprehensions |||

          (* case expressions *)
          (fn () =>
              if (is_const f andalso (!prettyprint_cases)) then
                case grammar_name G f of
                  SOME "case" =>
                  (let
                     val (split_on, splits) = convert_case tm
                     val parens = (case rgrav of Prec _ => true | _ => false)
                                  orelse
                                  combpos = RandCP
                     fun p body =
                         get_gspec >-
                         (fn b => if b orelse parens then
                                    add_string "(" >> body >> add_string ")"
                                  else
                                    body)
                     val casebar = add_break(1,0) >> add_string "|" >> hardspace 1
                     fun do_split rprec (l,r) =
                         record_bvars
                             (free_vars l)
                             (block PP.CONSISTENT 0
                                    (pr_term l Top Top Top (decdepth depth) >>
                                     hardspace 1 >>
                                     add_string "=>" >> add_break(1,2) >>
                                     pr_term r Top Top rprec (decdepth depth)))
                   in
                     p (block PP.CONSISTENT 0
                          (block PP.CONSISTENT 0
                            (add_string "case" >> add_break(1,2) >>
                             pr_term split_on Top Top Top (decdepth depth) >>
                             add_break(1,0) >> add_string "of") >>
                           add_break (1,2) >>
                           (if length splits > 1 then
                              pr_list (do_split (Prec(0,"casebar")))
                                      casebar
                                      (butlast splits) >>
                              casebar >>
                              do_split (if parens then Top else rgrav)
                                      (last splits)
                            else
                              do_split (if parens then Top else rgrav)
                                       (hd splits))))
                   end handle CaseConversionFailed => fail)
                | _ => fail
              else fail) |||

          (* let expressions *)
          (fn () => if is_let tm then pr_let lgrav rgrav tm else fail) |||

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
  fn pps => fn t =>
    let
      val baseppfns = smpp.from_backend backend
      val {add_string,add_break,ublock,add_xstring,add_newline,ustyle,...} =
          baseppfns
      val (add_string, add_xstring, add_break) =
          avoid_merge (add_string, add_xstring, add_break)
      val ppfns = {add_string = add_string,
                   add_xstring = add_xstring,
                   add_break = add_break,
                   add_newline = add_newline,
                   ublock = block,
                   ustyle = ustyle}
    in
       begin_block pps CONSISTENT 0;
       case pr_term false
                    (!Globals.show_types orelse !Globals.show_types_verbosely)
                    (!Globals.show_types_verbosely)
                    ppfns NoCP t RealTop RealTop RealTop
                    (!Globals.max_print_depth)
                    (start_info,pps)
        of
         NONE => HOL_WARNING "term_pp" "pp_term" "Monadic printer returned NONE"
       | SOME _ => ();
       end_block pps
    end
end

end; (* term_pp *)
