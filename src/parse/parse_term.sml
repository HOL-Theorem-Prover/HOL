structure parse_term :> parse_term =
struct

open Lib
open errormonad term_tokens term_grammar HOLgrammars
open GrammarSpecials
infix >> >- ++ >->

val syntax_error_trace = ref true
val _ = Feedback.register_btrace ("syntax_error", syntax_error_trace)

fun WARN f msg = if !syntax_error_trace then
                   Feedback.HOL_WARNING "parse_term" f msg
                 else ()
fun WARNloc f loc msg = if !syntax_error_trace then
                          Feedback.HOL_WARNINGloc "parse_term" f loc msg
                        else ()

fun noloc s = (s, locn.Loc_None)
fun qfail x = error (noloc "") x
fun WARNloc_string loc s = (s, loc)



exception Failloc of (locn.locn * string)
fun FAILloc locn s = raise Failloc (locn, s)

fun liftlocn f (x,locn) = (f x,locn)

exception ParseTermError of string locn.located
type 'a token = 'a term_tokens.term_token
type 'a qbuf = 'a qbuf.qbuf


fun insert_sorted (k, v) [] = [(k, v)]
  | insert_sorted kv1 (wholething as (kv2::rest)) = let
      val (k1, _) = kv1
      val (k2, _) = kv2
    in
      if (k1 < k2) then kv1::wholething
      else kv2::insert_sorted kv1 rest
    end


fun listtoString f [] = "[]"
  | listtoString f xs = let
      fun lf [x] = f x
        | lf (x::xs) = f x ^ ", " ^ lf xs
        | lf _ = raise Fail "Can't happen"
    in
      "[" ^ lf xs ^ "]"
    end

fun fragtoString (QUOTE s) = s
  | fragtoString (ANTIQUOTE _) = " ^... "
fun quotetoString [] = ""
  | quotetoString (x::xs) = fragtoString x ^ quotetoString xs


datatype 'a varstruct
  = SIMPLE of string
  | VPAIR of ('a varstruct locn.located * 'a varstruct locn.located)
  | TYPEDV of 'a varstruct locn.located * Pretype.pretype locn.located
  | RESTYPEDV of 'a varstruct locn.located * 'a preterm locn.located
  | VS_AQ of 'a
and 'a preterm
  = COMB of ('a preterm locn.located * 'a preterm locn.located)
  | VAR of string
  | QIDENT of string * string
  | ABS of ('a varstruct locn.located * 'a preterm locn.located)
  | AQ of 'a
  | TYPED of ('a preterm locn.located * Pretype.pretype locn.located)

infix --
fun (l1 -- []) = l1
  | (l1 -- (x::xs)) = List.filter (fn y => y <> x) l1 -- xs

fun all_tokens strlist =
  map STD_HOL_TOK strlist @ [BOS, EOS, Id, TypeColon, TypeTok, EndBinding]

exception PrecConflict of stack_terminal * stack_terminal

val complained_already = ref false;

fun first_tok [] = raise Fail "Shouldn't happen parse_term 133"
  | first_tok (RE (TOK s)::_) = s
  | first_tok (_ :: t) = first_tok t

structure Polyhash =
struct
   fun peek (ref dict) k = Binarymap.peek(dict,k)
   fun peekInsert (r as ref dict) (k,v) =
       case Binarymap.peek(dict,k) of
         NONE => (r := Binarymap.insert(dict,k,v); NONE)
       | x => x
   fun insert (r as ref dict) (k,v) =
       r := Binarymap.insert(dict,k,v)
   fun listItems (ref dict) = Binarymap.listItems dict
   fun mkDict cmp = let
     val newref = ref (Binarymap.mkDict cmp)
   in
     newref
   end
end

local
  val rule_elements = term_grammar.rule_elements o #elements
in
fun rule_left (rr: rule_record) =
    case hd (rule_elements rr) of
      TOK s => STD_HOL_TOK s
    | _ => raise Fail ("rule list is bogus for "^ #term_name rr)
end

fun left_grabbing_elements rule =
    case rule of
      INFIX (STD_infix(rules, _)) => map rule_left rules
    | INFIX RESQUAN_OP => [ResquanOpTok]
    | INFIX (FNAPP rules) => STD_HOL_TOK fnapp_special :: map rule_left rules
    | INFIX VSCONS => [VS_cons]
    | SUFFIX (STD_suffix rules) => map rule_left rules
    | SUFFIX TYPE_annotation => [TypeColon]
    | _ => []

datatype mx_src = Ifx | Pfx | MS_Other | MS_Multi
datatype mx_order = PM_LESS of mx_src
                  | PM_GREATER of mx_src
                  | PM_EQUAL
                  | PM_LG of {pfx:order,ifx:order}
datatype order_compat_verdict = OK | Multify of mx_order | Bad
fun order_compat mx1 mx2 =
    case (mx1, mx2) of
      (PM_LESS src1, PM_LESS src2) => if src1 = src2 then OK
                                      else Multify (PM_LESS MS_Multi)
    | (PM_GREATER src1, PM_GREATER src2) => if src1 = src2 then OK
                                            else Multify (PM_GREATER MS_Multi)
    | (PM_EQUAL, _) => OK
    | (_, PM_EQUAL) => OK
    | (PM_LG i1, PM_LG i2) => if i1 = i2 then OK else Bad
    | (_ , _) => Bad

fun mx_order mxo =
    case mxo of
      PM_LESS _ => SOME LESS
    | PM_GREATER _ => SOME GREATER
    | PM_EQUAL => SOME EQUAL
    | PM_LG _ => NONE

val ambigrm = ref 1
val _ = Feedback.register_trace ("ambiguous grammar warning", ambigrm, 2)

fun mk_prec_matrix G = let
  exception NotFound = Binarymap.NotFound
  exception BadTokList
  type dict = ((stack_terminal * bool) * stack_terminal,
               mx_order) Binarymap.dict ref
  val {lambda, endbinding, type_intro, restr_binders, ...} = specials G
  val specs = grammar_tokens G
  val Grules = term_grammar.grammar_rules G
  val alltoks =
    ResquanOpTok :: VS_cons :: STD_HOL_TOK fnapp_special :: all_tokens specs
  val matrix: dict =
      Polyhash.mkDict (pair_compare(pair_compare(ST_compare,bool_compare),
                                    ST_compare))
      (* the bool is true if there is a non-terminal between the two
         terminal tokens.  E.g.,
           x + -y
         doesn't have such a space between the + and -, whereas
           x + z - y
         does (the z will be a non-terminal)
      *)

  val rule_elements = term_grammar.rule_elements o #elements
  val complained_this_iteration = ref false
  fun insert_bail k =
      (Polyhash.insert matrix (k, PM_LESS MS_Multi);
       complained_this_iteration := true;
       if not (!complained_already) andalso
          (!Globals.interactive orelse !ambigrm = 2)
       then let
           val msg = "Grammar ambiguous on token pair "^
                     STtoString G (#1 (#1 k)) ^ " and " ^
                     STtoString G (#2 k) ^ ", and "^
                     "probably others too"
         in
           case !ambigrm of
             0 => ()
           | 1 => (Feedback.HOL_WARNING "Parse" "Term" msg;
                   complained_already := true)
           | 2 => raise Feedback.mk_HOL_ERR "parse_term" "mk_prec_matrix" msg
           | _ => raise Fail "parse_term: matrix construction invariant fail!"
         end
       else
         ())
  fun insert k v = let
    val insert_result = Polyhash.peekInsert matrix (k, v)
    val raw_insert = Polyhash.insert matrix
  in
    case (insert_result, v) of
      (SOME PM_EQUAL, _) => ()  (* ignore this *)
    | (SOME _, PM_EQUAL) => raw_insert (k,v)  (* EQUAL overrides *)
    | (SOME oldv, _) => let
      in
        case order_compat oldv v of
          OK => ()
        | Multify v' => raw_insert (k, v')
        | Bad => let
            nonfix << >>
            val op >> = GREATER and op << = LESS
          in
            case (oldv,v) of
              (PM_LESS src1, PM_GREATER src2) => let
              in
                case (src1, src2) of
                  (Ifx, Pfx) => raw_insert (k, PM_LG {ifx= <<, pfx= >>})
                | (Pfx, Ifx) => raw_insert (k, PM_LG {ifx= >>, pfx= <<})
                | _ => insert_bail k
              end
            | (PM_GREATER src1, PM_LESS src2) => let
              in
                case (src1, src2) of
                  (Ifx,Pfx) => raw_insert (k, PM_LG {ifx= >>, pfx= <<})
                | (Pfx,Ifx) => raw_insert (k, PM_LG {ifx= <<, pfx= >>})
                | _ => insert_bail k
              end
            | _ => insert_bail k
          end
      end
    | (NONE, _) => ()
  end
  fun insert_eqs rule = let
    fun insert_oplist list = let
      fun recurse [] = raise BadTokList
        | recurse [x] = ()
        | recurse (TOK s1::(xs as TOK s2::_)) = let
          in
            insert ((STD_HOL_TOK s1, false), STD_HOL_TOK s2) PM_EQUAL;
            recurse xs
          end
        | recurse (TOK s1::TM::(xs as TOK s2::_)) = let
          in
            insert ((STD_HOL_TOK s1, true), STD_HOL_TOK s2) PM_EQUAL;
            recurse xs
          end
        | recurse l = raise Fail
                                (String.concat
                                     ("Bogus rule featuring elements "::
                                       separate " " (map reltoString l)))
    in
      recurse list
    end
  in
    case rule of
      PREFIX (STD_prefix rules) => app (insert_oplist o rule_elements) rules
    | PREFIX (BINDER slist) => let
        fun bindertok (BinderString {tok, ...}) = [tok]
          | bindertok LAMBDA = lambda
        val btoks = List.concat (map bindertok slist)
      in
        app (fn s => insert ((STD_HOL_TOK s, true), EndBinding) PM_EQUAL) btoks
      end
    | SUFFIX (STD_suffix rules) => app (insert_oplist o rule_elements) rules
    | SUFFIX TYPE_annotation => ()
    | INFIX (STD_infix (rules, _)) => app (insert_oplist o rule_elements) rules
    | INFIX RESQUAN_OP => ()
    | INFIX (FNAPP lst) => app (insert_oplist o rule_elements) lst
    | INFIX VSCONS => ()
    | CLOSEFIX rules => app (insert_oplist o rule_elements) rules
    | LISTRULE rlist => let
        fun process (r:listspec) = let
          val left = STD_HOL_TOK (first_tok (#leftdelim r))
          val right = STD_HOL_TOK (first_tok (#rightdelim r))
          val separator = STD_HOL_TOK (first_tok (#separator r))
        in
          insert ((left,false), right) PM_EQUAL;
          insert ((left,true), right) PM_EQUAL;
          insert ((left,true), separator) PM_EQUAL;
          insert ((separator,true), separator) PM_EQUAL;
          insert ((separator,true), right) PM_EQUAL
        end
      in
        app process rlist
      end
  end

  fun bi_insert (t1,t2) order = (insert ((t1,false), t2) order;
                                 insert ((t1,true), t2) order)
  (* the right hand end of a suffix or a closefix is greater than
     everything *)
  val closed_rhses = find_suffix_rhses G
  fun insert_rhs_relns () = let
    val all = alltoks
    val rhses = closed_rhses
  in
    app (fn rhs => app (fn t => bi_insert (rhs, t) (PM_GREATER MS_Other)) all)
        rhses
  end

  (* everything not a suffix rhs is less than the left hand end of a
     prefix/closefix *)
  val closed_lhses = find_prefix_lhses G
  fun insert_lhs_relns () = let
    val all = alltoks -- (EOS::closed_rhses)
  in
    app (fn lhs => app (fn t => insert ((t,false), lhs) (PM_LESS MS_Other))
                       all)
        closed_lhses
  end
  fun map_rule f [] = []
    | map_rule f (x::xs) = let
        val rest = map_rule f xs
        val here =
          case x of
            INFIX (STD_infix (rules, _)) => map (f o rule_elements) rules
          | INFIX (FNAPP rules) => map (f o rule_elements) rules
          | SUFFIX (STD_suffix rules) => map (f o rule_elements) rules
          | PREFIX (STD_prefix rules) => map (f o rule_elements) rules
          | CLOSEFIX rules => map (f o rule_elements) rules
          | LISTRULE rlist => let
              fun process (r:listspec) =
                [f (map (TOK o first_tok)
                        [#leftdelim r, #separator r, #rightdelim r])]
            in
              List.concat (map process rlist)
            end
          | _ => []
      in
        here @ rest
      end
  val first_tok = hd o List.mapPartial (fn TOK s => SOME s | _ => NONE)
  val last_tok = first_tok o List.rev
  val all_lhs =
    TypeColon::BOS::VS_cons::ResquanOpTok::Id::
    map STD_HOL_TOK (fnapp_special::(map_rule first_tok Grules))
  val all_rhs =
    TypeTok::EndBinding::EOS::VS_cons::ResquanOpTok::Id::
    map STD_HOL_TOK (fnapp_special::(map_rule last_tok Grules))
  (* Between things that are equal, the thing on the left is less than
     all possible left hand sides, and the thing on the right is
     greater than all possible right hand sides. *)
  fun calc_eqpairs() =
    List.mapPartial
        (fn (((t1,_),t2), v) => if v = PM_EQUAL then SOME (t1,t2) else NONE)
        (Polyhash.listItems matrix)
  fun terms_between_equals (k1, k2) = let
  in
    app (fn lhs => bi_insert (k1, lhs) (PM_LESS MS_Other)) all_lhs;
    app (fn rhs => bi_insert (rhs, k2) (PM_GREATER MS_Other)) all_rhs
  end

  (* now the tricky stuff where the precedence relation makes a difference *)
  (* if the rule might grab stuff to its left (is an infix or suffix),
     then add
        x > rule's left hand token
           for all x on right hand side of prefixes and infixes below
     if the rule might grab stuff to its right (is an infix or prefix)
     then add
        rule's right hand token < x
          for all x on left hand side of suffixes and infixes below *)
  fun rule_right (rr:rule_record) =
    case List.last (rule_elements rr) of
      TOK s => STD_HOL_TOK s
      | _ => raise Fail ("rule list is bogus for "^ #term_name rr)
  fun add2 v p = (p,v)
  fun right_grabbing_elements rule =
    case rule of
      INFIX(STD_infix(rules, _)) => map (add2 Ifx o rule_right) rules
    | INFIX RESQUAN_OP => [(ResquanOpTok,Ifx)]
    | INFIX(FNAPP rules) =>
        (STD_HOL_TOK fnapp_special,Ifx) :: map (add2 Ifx o rule_right) rules
    | INFIX VSCONS => [(VS_cons,Ifx)]
    | PREFIX (BINDER _) => [(EndBinding,Pfx)]
    | PREFIX (STD_prefix rules) => map (add2 Pfx o rule_right) rules
    | _ => []
  val GREATER' = PM_GREATER MS_Other
  val LESS' = PM_LESS MS_Other
  val EQUAL' = PM_EQUAL
  fun process_rule rule remainder =
    case rule of
      INFIX(STD_infix(rules, assoc)) => let
        val this_level_lefts = map rule_left rules
        val lower_rights = List.concat (map right_grabbing_elements remainder)
        val this_level_rights = map rule_right rules
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
      (* for infix rules, also need to add precedence relations if there is
       associativity *)
      in
        app (fn lefttok =>
                app
                    (fn (lower_right,src) =>
                        insert ((lower_right,true), lefttok) (PM_GREATER src))
                    lower_rights)
            this_level_lefts;
        app (fn righttok =>
                app
                    (fn lower_left => insert ((righttok,true), lower_left)
                                             (PM_LESS Ifx))
                    lower_lefts)
            this_level_rights;
        case assoc of
          LEFT => let
          in
            app (fn right_tok =>
                 app (fn left_tok => insert ((right_tok,true), left_tok)
                                            (PM_GREATER Ifx))
                 this_level_lefts)
            this_level_rights
          end
        | RIGHT => let
          in
            app (fn right_tok =>
                 app (fn left_tok => insert ((right_tok,true), left_tok)
                                            (PM_LESS Ifx))
                 this_level_lefts)
            this_level_rights
          end
        | NONASSOC => ()
      end
    | INFIX RESQUAN_OP => let
        val lower_rights = List.concat (map right_grabbing_elements remainder)
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
      in
        app (fn lower_right => insert((#1 lower_right,true), ResquanOpTok)
                                     GREATER')
            lower_rights;
        app (fn lower_left => insert((ResquanOpTok,true), lower_left) LESS')
            lower_lefts
      end
    | PREFIX (STD_prefix rules) => let
        val this_level_rights = map rule_right rules
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
      in
        app (fn right_tok =>
                app
                    (fn lower_left => insert ((right_tok,true), lower_left)
                                             (PM_LESS Pfx))
                    lower_lefts)
        this_level_rights
      end
    | PREFIX (BINDER _) => let
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
      in
        app (fn lower_left => insert ((EndBinding,true),lower_left) LESS')
            lower_lefts
      end
    | SUFFIX TYPE_annotation => let
        val lower_rights = List.concat (map right_grabbing_elements remainder)
      in
        app (fn (lower_right,src) =>
                insert ((lower_right,true), TypeColon) (PM_GREATER src))
            lower_rights
      end
    | SUFFIX (STD_suffix rules) => let
        val lower_rights = List.concat (map right_grabbing_elements remainder)
        val lefts = map rule_left rules
      in
        app (fn left_tok =>
             app (fn (lower_right,src) =>
                     insert ((lower_right,true), left_tok) (PM_GREATER src))
                 lower_rights)
            lefts
      end
    | INFIX (FNAPP rules) => let
        val lower_rights = List.concat (map right_grabbing_elements remainder)
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
        val this_level_lefts = map rule_left rules
        val this_level_rights = map rule_right rules
        val fnapp = STD_HOL_TOK fnapp_special
      in
        app (fn lower_left => insert ((fnapp,true), lower_left) LESS')
            lower_lefts;
        app (fn lower_right => insert ((#1 lower_right,true), fnapp) GREATER')
            lower_rights;
         (* function application left associative *)
        insert ((fnapp,true), fnapp) GREATER';
        app (fn other => insert ((other,true), fnapp) GREATER')
            this_level_rights;
        app (fn other => insert ((fnapp,true), other) GREATER')
            this_level_lefts;
        process_rule (INFIX(STD_infix (rules, LEFT))) remainder
      end
    | INFIX VSCONS => let
        val lower_rights = List.concat (map right_grabbing_elements remainder)
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
      in
        app (fn lower_left => insert ((VS_cons,true), lower_left) LESS')
            lower_lefts;
        app (fn lower_right => insert ((#1 lower_right,true), VS_cons) GREATER')
            lower_rights;
        (* kind of non-associative *)
        insert ((VS_cons,true), VS_cons) EQUAL'
      end
    | _ => ()
  fun apply_them_all f [] = ()
    | apply_them_all f (x::xs) = (f x xs ; apply_them_all f xs)
in
  app insert_eqs Grules ;
  insert ((BOS, true), EOS) EQUAL';
  app terms_between_equals (calc_eqpairs());
  (* these next equality pairs will never have terms interfering between
     them, so we can insert the equality relation between them after doing
     the above *)
  insert ((TypeColon,false), TypeTok) EQUAL';
  app (fn b => insert ((STD_HOL_TOK b,true), EndBinding) EQUAL') (binders G);
  insert_rhs_relns () ;
  insert_lhs_relns () ;
  apply_them_all process_rule Grules;
  if (not (!complained_this_iteration)) then complained_already := false
  else ();
  matrix
end

datatype rule_summary =
  infix_rule of string | prefix_rule of string | suffix_rule of string |
  closefix_rule of string | listfix_rule of {cons : string, nilstr : string}
fun summary_toString rs =
  case rs of
    infix_rule s => s
  | prefix_rule s => s
  | suffix_rule s => s
  | closefix_rule s => s
  | listfix_rule {cons, nilstr = n} => "List : {cons = "^cons^", nil = "^n^"}"


(* in addition to all of the rules that you'd expect due to the infix,
   prefix, suffix and closefix operators, we also add rules for the
   nil singleton, and doubleton cases of the list rules.  This
   increases efficiency for these relatively common cases, saving us
   an examination of the grammar when we come to do a reduction to
   spot whether a putative rhs is an instance of a list *)

fun mk_ruledb (G:grammar) = let
  val Grules = term_grammar.grammar_rules G
  val table:(rule_element list, rule_summary)Binarymap.dict ref =
       Polyhash.mkDict (Lib.list_compare RE_compare)
  fun insert_rule f g (rr:rule_record) =
    Polyhash.insert table (g (term_grammar.rule_elements (#elements rr)),
                           f (#term_name rr))
  fun infix_f elms = TM :: (elms @ [TM])
  fun suffix_f elms = TM :: elms
  fun closefix_f elms = elms
  fun prefix_f elms = elms @ [TM]
  fun addrule rule =
    case rule of
      INFIX (STD_infix(rules, _)) => app (insert_rule infix_rule infix_f) rules
    | INFIX RESQUAN_OP => ()
    | INFIX VSCONS => ()
    | INFIX (FNAPP rules) => let
      in
        Polyhash.insert table (infix_f [TOK fnapp_special],
                               infix_rule fnapp_special);
        app (insert_rule infix_rule infix_f) rules
      end
    | PREFIX (STD_prefix rules) => app (insert_rule prefix_rule prefix_f) rules
    | PREFIX (BINDER s) => ()
    | SUFFIX (STD_suffix rules) => app (insert_rule suffix_rule suffix_f) rules
    | SUFFIX TYPE_annotation => ()
    | CLOSEFIX rules => app (insert_rule closefix_rule closefix_f) rules
    | LISTRULE rlist => let
        fun process (r:listspec) = let
          val ldelim = TOK (first_tok (#leftdelim r))
          val rdelim = TOK (first_tok (#rightdelim r))
          val sep = TOK (first_tok (#separator r))
          val nil_pattern =   [ldelim, rdelim]
          val singleton_pat = [ldelim, TM, rdelim]
          val doubleton_pat = [ldelim, TM, sep, TM, rdelim]
          val insert = Polyhash.insert table
          val summary = listfix_rule {cons = #cons r, nilstr = #nilstr r}
        in
          insert (nil_pattern, summary);
          insert (singleton_pat, summary);
          insert (doubleton_pat, summary)
        end
      in
        app process rlist
      end
in
  app addrule Grules;
  table
end


fun mwhile B C =
  B >-  (fn b => if b then C >> mwhile B C else ok)

fun mif B C = B >- (fn b => if b then C else ok)

datatype 'a stack_item =
  Terminal of stack_terminal |
  NonTerminal of 'a preterm |
  NonTermVS of 'a varstruct locn.located list

fun is_terminal (Terminal _,_) = true
  | is_terminal _ = false
fun dest_terminal (Terminal x,_) = x
  | dest_terminal _ = raise Fail "dest_terminal not called on terminal"
fun is_nonterm t = not (is_terminal t)


datatype 'a lookahead_item =
  Token of 'a term_token | PreType of Pretype.pretype |
  LA_Symbol of stack_terminal

datatype vsres_state = VSRES_Normal | VSRES_VS | VSRES_RESTM

datatype 'a PStack =
  PStack of {stack : ('a stack_item locn.located * 'a lookahead_item) list,
             lookahead : 'a lookahead_item locn.located list,
             in_vstruct : (vsres_state * int) list}

(* dummy lookahead token *)
val XXX = Token (Ident "XXX")


fun pstack (PStack {stack, ...}) = stack
fun upd_stack (PStack {stack, lookahead, in_vstruct}) new =
  PStack{stack = new, lookahead = lookahead, in_vstruct = in_vstruct}
fun pla (PStack{lookahead,...}) = lookahead
fun upd_la (PStack {stack, lookahead, in_vstruct}) new =
  PStack{stack = stack, lookahead = new, in_vstruct = in_vstruct}
fun invstructp0 (PStack{in_vstruct,...}) = in_vstruct

fun fupd_hd f [] = []
  | fupd_hd f (x::xs) = f x :: xs

fun fupd_fst f (x,y) = (f x, y)
fun fupd_snd f (x,y) = (x, f y)

fun fupd_vs0 f (PStack{in_vstruct,lookahead,stack}) =
  PStack{stack = stack, lookahead = lookahead, in_vstruct = f in_vstruct}

fun invstructp (cs, p) = ((cs, p), Some (invstructp0 p))

fun inc_paren (cs, p) = ((cs, fupd_vs0 (fupd_hd (fupd_snd (fn n => n + 1))) p),
                         Some ())
fun dec_paren (cs, p) = ((cs, fupd_vs0 (fupd_hd (fupd_snd (fn n => n - 1))) p),
                         Some ())
fun enter_binder (cs,p) =
  ((cs, fupd_vs0 (fn rest => (VSRES_VS, 0)::rest) p), Some ())
fun enter_restm (cs, p) =
  ((cs, fupd_vs0 (fupd_hd (fupd_fst (K VSRES_RESTM))) p), Some ())
fun leave_restm (cs, p) =
  ((cs, fupd_vs0 (fupd_hd (fupd_fst (K VSRES_VS))) p), Some ())
fun leave_binder (cs, p) = ((cs, fupd_vs0 tl p), Some ())

fun push_pstack p i = upd_stack p (i::pstack p)
fun top_pstack p = hd (pstack p)
fun pop_pstack p = upd_stack p (tl (pstack p))

fun push t (cs, p) = ((cs, push_pstack p t), Some ())
fun topterm (cs, p) =
  ((cs, p), case List.find (is_terminal o #1) (pstack p) of
              NONE => Error (noloc "No terminal in stack")
            | SOME x => Some x)
fun pop (cs, p) =
    ((cs, pop_pstack p), Some (top_pstack p))
    handle Empty => ((cs, p), Error (noloc "pop: empty stack"))
fun getstack (cs, p) = ((cs, p), Some (pstack p))


fun set_la tt (cs, p) = ((cs, upd_la p tt), Some ())
fun current_la (cs, p) = ((cs, p), Some (pla p))

fun findpos P [] = NONE
  | findpos P (x::xs) = if P x then SOME(0,x)
                        else Option.map (fn (n,x) => (n + 1, x)) (findpos P xs)

fun parse_term (G : grammar) typeparser = let
  val Grules = grammar_rules G
  val {type_intro, lambda, endbinding, restr_binders, res_quanop} = specials G
  val num_info = numeral_info G
  val overload_info = overload_info G
  val closed_lefts = find_prefix_lhses G
  val left_grabbers = List.concat (map left_grabbing_elements Grules)
  val fnapp_closed_lefts = Lib.subtract closed_lefts left_grabbers
  val _ =
      isSome (findpos (fn (SUFFIX TYPE_annotation) => true | _ => false)
                      Grules)
      orelse raise Fail "Grammar must allow type annotation"
  val prec_matrix = mk_prec_matrix G
  val rule_db = mk_ruledb G
  val is_binder = is_binder G
  val binder_table = let
    fun recurse (r, acc) =
        case r of
          PREFIX (BINDER blist) => let
            fun irec (b, acc) =
                case b of
                  LAMBDA => acc
                | BinderString {term_name, tok, ...} =>
                    Binarymap.insert(acc,tok,term_name)
          in
            List.foldl irec acc blist
          end
        | _ => acc
  in
    List.foldl recurse (Binarymap.mkDict String.compare) Grules
  end
  fun term_name_for_binder s = Binarymap.find(binder_table,s)
  val grammar_tokens = term_grammar.grammar_tokens G
  val lex  = let
    val specials = endbinding::grammar_tokens @ term_grammar.known_constants G
    val ttlex = term_tokens.lex specials
  in
    fn (qb, ps) =>
       case ttlex qb of
         NONE => ((qb, ps), Error (noloc "Token-lexing failed"))
       | SOME t => ((qb, ps), Some t)
  end
  fun lifted_typeparser (qb, ps) = ((qb, ps), Some (typeparser qb))


  val keyword_table =
      HOLset.addList(HOLset.empty String.compare, grammar_tokens)

  (* transform takes an input token (of the sort that comes out of the
     lexer), and turns it into a token of the sort used internally by the
     parser. *)
  fun transform (in_vs as (vs_state, nparens))
                (t:'a lookahead_item locn.located option) =
    case t of
      NONE => (EOS, locn.Loc_None, NONE)
    | SOME (tt as Token x,locn) => let
      in
        case x of
          Ident s =>
            if String.sub(s,0) = #"$" then let
                val locn = locn.move_start 1 locn
              in
              (Id, locn, SOME (Token (Ident (String.extract(s,1,NONE))))) end
            else if s = res_quanop andalso vs_state = VSRES_VS then
              (ResquanOpTok, locn, SOME tt)
            else if s = type_intro then (TypeColon, locn, SOME tt)
            else if s = vs_cons_special then (VS_cons, locn, SOME tt)
            else if s = endbinding andalso nparens = 0 andalso
              vs_state <> VSRES_Normal then (EndBinding, locn, SOME tt)
            else if HOLset.member(keyword_table, s) then
              (STD_HOL_TOK s, locn, SOME tt)
            else (Id, locn, SOME tt)
        | Antiquote _ => (Id, locn, SOME tt)
        | Numeral _ => (Id, locn, SOME tt)
        | QIdent _ => (Id, locn, SOME tt)
      end
    | SOME (tt as PreType ty,locn) => (TypeTok, locn, SOME tt)
    | SOME (tt as LA_Symbol st,locn) => (st, locn, SOME tt)

  (* find the initial segment of the stack such that all of the segment
     has the equality relation between components and such that the first
     element not in the segment is less than than the last one in the
     segment *)
  (* NB: the FAILloc invocations in this function raise Failloc exceptions that
         are trapped at the bottom of the perform_reduction function *)
  fun find_reduction stack =
    case stack of
      [] => raise Fail "find_reduction: stack empty!"
    | [_] => raise Fail "find_reduction: stack singleton!"
    | ((t1 as ((Terminal x1,x1locn), _))::rest) => let
      in
        case rest of
          [] => FAILloc x1locn "find_reduction : impossible"
        | (((Terminal x2,x2locn), _)::_) => let
            val res = valOf (Polyhash.peek prec_matrix ((x2,false),x1))
              handle Option =>
                FAILloc (locn.between x2locn x1locn)
                        ("No relation between "^STtoString G x2^" and "^
                         STtoString G x1)
          in
            case res of
              PM_LESS _ => [t1]
            | PM_EQUAL =>  (t1::find_reduction rest)
            | PM_LG _ => [t1]
                         (* must be a less, because a greater is impossible *)
            | PM_GREATER _ => FAILloc (locn.between x2locn x1locn)
                                      "find_reduction: found a greater on stack"
          end
        | ((t2 as ((_,t2locn),_))::rest2) => let
            (* t2 is a non-terminal, whether VS or not *)
          in
            case rest2 of
              [] => FAILloc t2locn "find_reduction : nonterminal at stack base!"
            | (((Terminal x2,x2locn), _)::_) => let
                val res = valOf (Polyhash.peek prec_matrix ((x2,true), x1))
                  handle Option =>
                    FAILloc (locn.between x2locn t2locn)
                            ("No relation between "^STtoString G x2^" and "^
                             STtoString G x1)
              in
                case res of
                  PM_LESS _ => [t1,t2]
                | PM_EQUAL => t1::t2::find_reduction rest2
                | PM_LG _ => [t1,t2]
                | PM_GREATER _ => FAILloc (locn.between x2locn t2locn)
                                          "find_reduction: greater on stack!"
              end
            | (((_,locn),_)::_) => FAILloc (locn.between locn t2locn) "find_reduction 2 NTs!"
          end
      end
    | (t1::rest) => t1::find_reduction rest (* t1 a non-terminal *)

  (* given an initial segment of the stack that corresponds to a reduction,
     determine whether or not this corresponds to a rule, and if it does
     pull the tokens of the stack and replace them with the right
     non-terminal *)
  fun perform_reduction rhs = let
    fun ok_item ((Terminal (STD_HOL_TOK _),_), _) = true
      | ok_item ((NonTerminal _,_), _) = true
      | ok_item _ = false

    (* what follows is only called on what will be list RHSes of
     length greater than two, as smaller lists will have been caught
     by the insertion of these rules specifically into the DB. *)

    fun handle_list_reduction rhs = let
      exception Hah
      fun possible_list pattern = let
        val _ = length pattern >= 5 orelse raise Hah
        val poss_left = case (hd pattern) of TOK x => x | _ => raise Hah
        val poss_right =
          case (List.last pattern) of TOK x => x | _ => raise Hah
        fun butlast [x] = []
          | butlast [] = raise Fail "butlast: shouldn't happen"
          | butlast (x::xs) = x::butlast xs
        val interior = butlast (tl pattern)
        val poss_sep =
          case (List.nth(interior, 1)) of TOK x => x | _ => raise Hah
        fun list_ok [] = raise Fail "list_ok: shouldn't happen"
          | list_ok [TM] = true
          | list_ok (TOK _::_) = false
          | list_ok (TM :: TOK s :: rest) = s = poss_sep andalso list_ok rest
          | list_ok (TM :: TM :: _) = false
      in
        if list_ok interior then
          term_grammar.compatible_listrule G {separator = poss_sep,
                                              leftdelim = poss_left,
                                              rightdelim = poss_right}
        else
          NONE
      end handle Hah => NONE
    in
      Option.map listfix_rule (possible_list rhs)
    end
  in
    if List.all ok_item rhs then let
      (* it's important to remember that the left end of the possible
         RHS might have looked like   TOK s1 -- TM -- TOK s2, and that
         in this case there will be s1 < s2 in the precedence matrix, but
         that TM will always have been popped in this case.

         This may or may not be appropriate.  If the RHS is a suffix thing
         or an infix, then that TM is part of the reduction, otherwise it
         isn't, and should be left on the stack.

         Below, the variable top_was_tm is true if a TM was popped in this
         way. *)
      (* NB: terminology: each stack item is either a TM (=term, i.e.,
         nonterminal) or a TOK (=token, i.e., terminal). *)
      fun stack_item_to_rule_element (Terminal (STD_HOL_TOK s),_) = TOK s
        | stack_item_to_rule_element (NonTerminal _,_) = TM
        | stack_item_to_rule_element (_,locn) = FAILloc locn "perform_reduction: gak!"
      val ((_,rlocn),_) = List.hd rhs
      val rhs = List.rev rhs
      val translated_rhs = map (stack_item_to_rule_element o #1) rhs
      val ((_,llocn),_) = List.hd rhs
      val lrlocn = locn.between llocn rlocn
      val top_was_tm = hd translated_rhs = TM
      val rule = let
        val errmsg = "No rule for "^ listtoString reltoString translated_rhs
      in
        case Polyhash.peek rule_db translated_rhs of
          NONE => let
          in
            if top_was_tm then
              case Polyhash.peek rule_db (tl translated_rhs) of
                NONE => (valOf (handle_list_reduction (tl translated_rhs))
                         handle Option => FAILloc lrlocn errmsg)
              | SOME r => r
            else
              valOf (handle_list_reduction translated_rhs)
              handle Option => FAILloc lrlocn errmsg
          end
        | SOME r => r
      end
      val ignore_top_item =
          case rule of
              infix_rule   s => false
            | suffix_rule  s => false
            | _              => top_was_tm
      (* rhs' is the actual stack segment matched by the rule, and llocn' is
         its left edge, unlike rhs and llocn which may contain a spurious TM
         on the left *)
      val rhs' = if ignore_top_item then tl rhs else rhs
      val ((_,llocn'),_) = List.hd rhs'
      val lrlocn' = locn.between llocn' rlocn
      fun seglocs xs als mal =
          (* extract TM items, and locations of right edges of
             maximal initial segments containing them *)
          case (xs,mal) of
            ((((NonTerminal p,locn),_)::xs), NONE       ) => seglocs xs      als  (SOME((p,locn),locn))
          | ((((NonTerminal p,locn),_)::xs), SOME al    ) => seglocs xs (al::als) (SOME((p,locn),locn))
          | ((((_            ,locn),_)::xs), NONE       ) => seglocs xs als mal
          | ((((_            ,locn),_)::xs), SOME (pl,_)) => seglocs xs als (SOME(pl,locn))
          | ([]                            , NONE       ) => List.rev als
          | ([]                            , SOME al    ) => List.rev (al::als)
      val args_w_seglocs = seglocs rhs' [] NONE
      fun CCOMB((x,locn),y) = (COMB(y,x),locn.between (#2 y) locn)
      val newterm =
        case rule of
          listfix_rule r => let
            fun mk_list [] = (VAR (#nilstr r),rlocn)
              | mk_list ((x,_)::xs) = (COMB((COMB((VAR (#cons r),#2 x), x),
                                             #2 x),
                                            mk_list xs),
                                       locn.between (#2 x) rlocn)
          in
            mk_list args_w_seglocs
          end
        | _ =>
          List.foldl CCOMB (VAR (summary_toString rule),llocn') args_w_seglocs
    in
      repeatn (length rhs') pop >>
      push ((NonTerminal (#1 newterm),lrlocn'), XXX)
        (* lrlocn: force location to entire RHS, including tokens *)
    end
  else
    case rhs of
      (((Terminal Id,locn), tt as Token (Antiquote a))::_) => let
      in
        pop >> invstructp >-
        (fn inv =>
         if #1 (hd inv) = VSRES_VS then
           push ((NonTermVS [(VS_AQ a,locn)],locn), tt)
         else
           push ((NonTerminal (AQ a),locn), tt))
      end
    | (((Terminal Id,locn), Token tt)::_) => let
        exception Temp of string
      in
        pop >> invstructp >-
        (fn inv => let
          val thing_to_push =
            case (#1 (hd inv), tt) of
              (VSRES_VS, Numeral _) => let
              in
                raise Temp "can't have numerals in binding positions"
              end
            | (_, Numeral(dp, copt)) => let
                val numeral_part =
                  Literal.gen_mk_numeral
                       {mk_comb  = fn (x,y) => (COMB(x,y),locn),
                        ZERO     = (QIDENT ("num"       , "0"      ),locn),
                        ALT_ZERO = (QIDENT ("arithmetic", "ZERO"   ),locn),
                        NUMERAL  = (QIDENT ("arithmetic", "NUMERAL"),locn),
                        BIT1     = (QIDENT ("arithmetic", "BIT1")  ,locn),
                        BIT2     = (QIDENT ("arithmetic", "BIT2")  ,locn)}
                       dp
                fun inject_np NONE = numeral_part
                  | inject_np (SOME s) = (COMB((VAR s,locn), numeral_part),locn)
              in
                case copt of
                  SOME c => let
                    val injector = List.find (fn (k,v) => k = c) num_info
                  in
                    case injector of
                      NONE => let
                      in
                        raise Temp ("Invalid suffix "^str c^ " for numeral")
                      end
                    | SOME (_, strop) => liftlocn NonTerminal (inject_np strop)
                  end
                | NONE =>
                  if null num_info then
                    if dp = Arbnum.zero then
                      (WARN "term_parser"
                       ("\n   0 treated specially and allowed - "^
                        "no other numerals permitted");
                      liftlocn NonTerminal (inject_np NONE))
                    else
                       raise Temp "No numerals currently allowed"
                  else let
                    val fns = fromNum_str
                  in
                    if Overload.is_overloaded overload_info fns then
                      liftlocn NonTerminal (inject_np (SOME fns))
                    else
                       raise Temp ("No overloadings exist for "^fns^
                                   ": use character suffix for numerals")
                      (* NonTerminal (inject_np (#2 (hd num_info))) *)
                  end
              end
            | (VSRES_VS, _) => (NonTermVS [(SIMPLE (token_string tt),locn)],locn)
            | (_, QIdent x) => (NonTerminal (QIDENT x),locn)
            | _ => (NonTerminal (VAR (token_string tt)),locn)
              (* tt is not an antiquote because of the wider context;
                 antiquotes are dealt with in the wider case statement
                 above *)
        in
           push (thing_to_push, Token tt)
        end handle Temp s => (WARNloc "parse_term" locn s;
                              error (WARNloc_string locn s)))
      end
    | (((Terminal TypeTok,rlocn), PreType ty)::((Terminal TypeColon,_), _)::
       ((NonTerminal t,llocn), _)::rest) => let
      in
        repeatn 3 pop >>
        push ((NonTerminal (TYPED ((t,llocn), (ty,rlocn))),
               locn.between llocn rlocn),
              XXX)
      end
    | (((Terminal TypeTok,rlocn), PreType ty)::((Terminal TypeColon,_), _)::
       ((NonTermVS vsl,llocn), _)::rest) => let
       in
         repeatn 3 pop >>
         push ((NonTermVS
                    (map (fn (v as (_,locn)) => (TYPEDV(v,(ty,rlocn)),locn))
                         vsl),
                    locn.between llocn rlocn),
               XXX)
       end
    | [((Terminal TypeTok,rlocn), PreType ty), ((Terminal TypeColon,_), _)] =>
      let
        val nonterm0 = (QIDENT("bool", "the_value"), rlocn)
        val type_annotation =
            (Pretype.Tyop{Thy="bool", Tyop = "itself", Args = [ty]},
             rlocn)
      in
        pop >> pop >>
        push ((NonTerminal (TYPED(nonterm0, type_annotation)), rlocn), XXX)
      end
    | (((NonTerminal t,rlocn), _)::((Terminal EndBinding,_), _)::
       ((NonTermVS vsl,_), _)::((Terminal (STD_HOL_TOK binder),llocn), _)::
       rest) => let
        exception Urk of string in let
        fun has_resq (v,_) =
          case v of
            VPAIR(v1, v2) => has_resq v1 orelse has_resq v2
          | TYPEDV(v0, ty) => has_resq v0
          | RESTYPEDV _ => true
          | _ => false
        fun has_tupled_resq (VPAIR(v1, v2),_) = has_resq v1 orelse has_resq v2
          | has_tupled_resq (TYPEDV(v0, _),_) = has_tupled_resq v0
          | has_tupled_resq (RESTYPEDV(v0, _),_) = has_tupled_resq v0
          | has_tupled_resq _ = false
        fun ERROR s1 s2 = Urk (s1^": "^s2)
        fun extract_resq (v,_) =
          case v of
            TYPEDV (v0, _) => extract_resq v0
          | RESTYPEDV(v0, t) => let
              val sub_resq = extract_resq v0
            in
              case sub_resq of
                NONE => SOME(v0, t)
              | SOME _ =>
                  raise ERROR "parse_term"
                    "Can't have double restricted quantification"
            end
          | _ => NONE
        fun comb_abs_fn(v,t) = let
          val binder = term_name_for_binder binder
        in
          if has_tupled_resq v then
            raise ERROR "parse_term"
                        "Can't have restricted quantification on nested \
                        \arguments"
          else
            case extract_resq v of
              NONE => (COMB((VAR binder,llocn),
                            (ABS(v, t),locn.between (#2 v) (#2 t))),
                       locn.between llocn rlocn)
            | SOME (v',P) => let
              in
                (COMB((COMB((VAR (Lib.assoc (SOME binder) restr_binders),llocn),
                            P),locn.between llocn (#2 P)),
                      (ABS(v', t),locn.between (#2 v') (#2 t))),
                 locn.between llocn rlocn)
                handle Feedback.HOL_ERR _ =>
                       raise ERROR "parse_term"
                                   ("No restricted quantifier associated with "
                                    ^binder)
              end
        end
        fun abs_fn (v,t) =
          if has_tupled_resq v then
            raise ERROR "parse_term"
              "Can't have restricted quantification on nested arguments"
          else
            case extract_resq v of
              NONE => (ABS(v,t),locn.between llocn rlocn)
            | SOME(v', P) =>
                (COMB((COMB((VAR (Lib.assoc NONE restr_binders),llocn),
                            P), locn.between llocn (#2 P)),
                      (ABS(v', t),locn.between (#2 v') (#2 t))),
                 locn.between llocn rlocn)
                handle Feedback.HOL_ERR _ =>
                  raise ERROR "parse_term"
                    "No restricted quantifier associated with lambda"
        val vsl = List.rev vsl
        val abs_t =
          List.foldr (if mem binder lambda then abs_fn else comb_abs_fn)
                     (t,rlocn) vsl
      in
        repeatn 4 pop >> push (liftlocn NonTerminal abs_t, XXX)
      end handle Urk s => (WARNloc "parse_term" (locn.between llocn rlocn) s;
                           error (WARNloc_string (locn.between llocn rlocn) s))
      end
    | (((Terminal(STD_HOL_TOK ")"),rlocn), _)::(vsl as ((NonTermVS _,_),_))::
       ((Terminal(STD_HOL_TOK "("),llocn), _)::rest) => let
      in
        (* need a rule here because
             1. a NonTermVS makes this a non-standard rule; and
             2. bracket-removal in the remove_specials code won't see
                the parentheses in the binding "var-struct" position
        *)
        repeatn 3 pop >>
        push vsl  (* don't bother expanding locn; would add no useful info *)
      end
    | (((NonTermVS vsl1,rlocn), _)::((Terminal(STD_HOL_TOK ","),_), _)::
       ((NonTermVS vsl2,llocn), _)::rest) => let val lrlocn = locn.between llocn rlocn
       in
         if length vsl1 <> 1 orelse length vsl2 <> 1 then let
             val msg = "Can't have lists of atoms as arguments to , in binder"
           in
             (WARNloc "parse_term" lrlocn msg;
              error (WARNloc_string lrlocn msg))
           end
         else
           repeatn 3 pop >>
           push ((NonTermVS [(VPAIR(hd vsl2, hd vsl1),lrlocn)],lrlocn), XXX)
       end
    | (((NonTerminal t,rlocn), _)::((Terminal ResquanOpTok,_), _)::
       ((NonTermVS vsl,llocn), _)::rest) => let
      in
         repeatn 3 pop >>
         push ((NonTermVS
                  (map (fn (v as (_,locn))=>
                           (RESTYPEDV(v,(t,rlocn)),locn)) vsl),
                  locn.between llocn rlocn),
               XXX) >>
         leave_restm
      end
    | _ => let
      fun is_vcons_list [] = false
        | is_vcons_list [x] = false
        | is_vcons_list (((NonTermVS _,_), _)::((Terminal VS_cons,_), _)::rest) = let
          in
            case rest of
              [((NonTermVS _,_),_)] => true
            | _ => is_vcons_list rest
          end
        | is_vcons_list _ = false
      fun get_vsls ((NonTermVS vsl,_), _) = SOME vsl | get_vsls _ = NONE
      val ((_,rlocn),_) = List.hd rhs
      val ((_,llocn),_) = List.last rhs
      val lrlocn = locn.between llocn rlocn
    in
      if is_vcons_list rhs then
        repeatn (length rhs) pop >>
        push ((NonTermVS(List.concat (List.mapPartial get_vsls rhs)),lrlocn),
              XXX)
      else
        (WARNloc "parse_term" lrlocn "Can't do this sort of reduction";
         error (WARNloc_string lrlocn "Can't do this sort of reduction"))
    end
  end handle Failloc (loc,s) =>
             (if !syntax_error_trace then
                (print (locn.toString loc);
                 print ":\n";
                 print s;
                 print "\n")
              else ();
              error (WARNloc_string loc s))


  val do_reduction =
    getstack >- (return o find_reduction) >- perform_reduction


  fun el2list x = [x]
  (* calls the lexer and puts the result onto the lookahead list *)
  val get_item = (lex >- set_la o el2list o liftlocn Token) ++ (set_la [])

  (* takes the top (first) terminal from the lookahead list (there is
     assumed to be one), and transfers it to the stack.  If this
     empties the lookahead list, then this is replenished by calling
     the appropriate lexer *)

  val shift =
    current_la >-
    (fn la => invstructp >- (return o hd) >-
     (fn in_vs =>
      case la of
        [] => error (noloc "No lookahead")
      | (x0::xs) => let
          val (terminal,locn,x) = transform in_vs (SOME x0)
        in
          push ((Terminal terminal,locn), valOf x) >>
          (if null xs then get_item else set_la xs) >>
             (case terminal of
                STD_HOL_TOK s =>
                  if is_binder s then enter_binder
                  else if s = "(" andalso #1 in_vs <> VSRES_Normal then
                    inc_paren
                  else if s = ")" andalso #1 in_vs <> VSRES_Normal then
                    dec_paren
                  else ok
              | ResquanOpTok => enter_restm
              | EndBinding => leave_binder
              | _ => ok)
        end))


  fun doit (tt, (top_item, top_token), in_vs) = let
    val (input_term, itlocn, _) = transform (hd in_vs) tt
    val top = dest_terminal top_item
    val toplocn = #2 top_item
    val ttt = Terminal input_term
    fun check_for_fnapp_insert stack =
      (* if the next thing in the lookahead might begin a whole new phrase,
         i.e. is a closed lhs, and the top thing on the stack is a non-terminal
         then we should insert the magical function application operator *)
        case stack of
          ((NonTerminal _,locn), _)::_ => let
            val fnt = (LA_Symbol (STD_HOL_TOK fnapp_special),locn.Loc_Near locn)
          in
            if mem input_term fnapp_closed_lefts then
              current_la >- (fn oldla => set_la (fnt::oldla))
            else
              qfail
          end
        | ((NonTermVS _,locn), _) :: _ => let
            val fnt = (LA_Symbol VS_cons,locn.Loc_Near locn)
          in
            if mem input_term fnapp_closed_lefts then
              current_la >- (fn oldla => set_la (fnt::oldla))
            else
              qfail
          end
        | _ => qfail

    (* a "paren escape" is a CAML style escaping of what would otherwise
       be a special token by parenthesising it.  Thus (/\) instead of $/\.
       The analysis is done at this level rather than inside the lexer to
       allow for white-space etc.  People will have to write ( * ) to escape
       the multiplication symbol, because without the space, it will look like
       a comment *)
    val check_for_paren_escape = let
      fun require (s:string option) =
          getstack >-
          (fn [] => error (noloc "Stack empty")
            | (tt :: _ ) => let
              in
                case tt of
                  ((Terminal (STD_HOL_TOK s'),locn), _) => let
                  in
                    case s of
                      NONE => pop >> return (s',locn)
                    | SOME s'' =>
                        if s' = s'' then pop >> return (s',locn)
                        else error (WARNloc_string
                                       locn
                                       ("Expected "^s''^", found "^s'))
                  end
                | _ => error (noloc "Expected a terminal")
              end)
    in
      if input_term = STD_HOL_TOK ")" then
          require NONE >-
          (fn (s,_) =>
              if s = ")" orelse s = "(" then
                qfail (* don't want to paren-escape "())" or  "(()" *)
              else
                require (SOME "(") >-
                (fn (_,locn) => let val lrlocn = locn.between locn itlocn
                  in
                  shift >> pop >>
                  (if is_binder s then leave_binder else return ()) >>
                  invstructp >- (return o #1 o hd) >-
                  (fn vstate =>
                      if vstate <> VSRES_VS then
                        push ((NonTerminal (VAR s),lrlocn), XXX)
                      else
                        push ((NonTermVS [(SIMPLE s,lrlocn)],lrlocn), XXX))
                  end ))
      else qfail
    end
    fun top_might_be_infix stk =
        case stk of
          ((NonTerminal _, _), _) :: ((Terminal _, _), _) ::
          ((NonTerminal _, _), _) :: _ => true
        | _ => false

    val usual_action = let
      fun get_topntp stk =
          case stk of
            [] => return (false,stk)
          | ((Terminal _,_), _) :: _ => return (false,stk)
          | _ => return (true,stk)
      fun check_order (topntp,stk) =
          case Polyhash.peek prec_matrix ((top,topntp), input_term) of
            NONE => let
              val msg = "Don't expect to find a "^STtoString G input_term^
                        " in this position after a "^STtoString G top^"\n"^
                        locn.toString itlocn^" and " ^
                        locn.toString toplocn^".\n"
            in
              if !syntax_error_trace then print msg
              else ();
              error (msg, toplocn)
            end
          | SOME order => let
              fun byorder GREATER = do_reduction
                | byorder _ = shift
            in
              case mx_order order of
                SOME x => byorder x
              | NONE => let
                  val (pfx,ifx) =
                      case order of
                        PM_LG {pfx,ifx} => (pfx,ifx)
                      | _ => raise Fail "parse_term: check_order invariant fail"
                in
                  if top_might_be_infix stk then byorder ifx
                  else byorder pfx
                end
            end
    in
      check_for_paren_escape ++
      (getstack >- check_for_fnapp_insert) ++
      (getstack >- get_topntp >- check_order)
    end
  in
    case input_term of
      TypeColon => let
      (* behaviour has to be slightly tricksy in this case:
           - we need to make sure that the next thing that appears in
             the stream of tokens is a complete type.
           - The way we do this is by calling the type parser on the
             remaining input stream and putting the result into the
             lookahead list behind the colon.
           - We only do this once, so the following action checks to
             see that the lookahead list is only one long, otherwise
             it can do the normal action
       *)
        fun action_on_la la =
          case la of
            [x as (_,locn)] =>
              lifted_typeparser >-  (fn ty => set_la [x, (PreType ty,locn.Loc_Near locn)])
              (* TODO: if lifted_typeparser returned a location, use that *)
          | _ => usual_action
      in
        current_la >- action_on_la
      end
    | STD_HOL_TOK s => usual_action
    | _ => usual_action
  end

  val current_input =
    current_la >-                   (fn lal =>    (* lookahead list *)
    if null lal then return NONE else return (SOME (hd lal)))


  val basic_action =
    current_input >-                (fn tt (* term token *) =>
    topterm >-                      (fn top =>
    invstructp >-                   (fn invs =>
    doit (tt, top, invs))))
in
  push ((Terminal BOS,locn.Loc_None), XXX) >> get_item >>
  mwhile (current_input >-
          (fn optt => if (isSome optt) then return true
                      else
                        (topterm >- (fn t =>
                         return (#1 (#1 t) <> Terminal BOS)))))
         basic_action
end

val initial_pstack = PStack {stack = [], lookahead = [],
                             in_vstruct = [(VSRES_Normal, 0)]}

fun is_final_pstack p =
  case p of
    PStack {stack = [((NonTerminal pt,_), _), ((Terminal BOS,_), _)],
            lookahead = [], in_vstruct = [(VSRES_Normal, 0)]} => true
  | _ => false

val recupd_errstring =
  "Record list must have (fld := value) or (fld updated_by f) elements only"

fun to_vabsyn vs =
  case vs of
    (SIMPLE x,locn) => Absyn.VIDENT (locn,x)
  | (VPAIR(v1,v2),locn) => Absyn.VPAIR(locn,to_vabsyn v1, to_vabsyn v2)
  | (TYPEDV(v,(ty,_)),locn) => Absyn.VTYPED(locn,to_vabsyn v, ty)
  | (VS_AQ x,locn) => Absyn.VAQ (locn,x)
  | (RESTYPEDV _,locn) =>
      raise ParseTermError
        ("Attempt to convert a vstruct still containing a RESTYPEDV",locn)

fun remove_specials t =
  case #1 t of
    COMB (t1, t2) => let
      open Absyn
    in
      case #1 t1 of
        VAR s => if s = bracket_special then remove_specials t2
                 else APP(#2 t, IDENT (#2 t1,s), remove_specials t2)
      | COMB ((VAR s,slocn), f) => let
        in
          if s = fnapp_special then APP(#2 t, remove_specials f, remove_specials t2)
          else if s = recsel_special then
            case #1 t2 of
              VAR fldname => APP(#2 t, IDENT (#2 t2, recsel_special ^ fldname),
                                 remove_specials f)
            | _ => raise ParseTermError
                ("Record selection must have single id to right \
                 \(possibly non-integer numeric literal)",#2 t2)
          else if s = reccons_special then
            remove_recupdate (#2 t) f t2 (IDENT (locn.Loc_None,"ARB"))
          else if s = recwith_special then
            remove_recupdate' (#2 t) t2 (remove_specials f)
          else
            if s = recupd_special orelse s = recfupd_special then
              raise ParseTermError
                ("May not use record update functions at top level \
                 \(possibly missing semicolon)",slocn)
            else
              APP(#2 t, remove_specials t1, remove_specials t2)
        end
      | _ => APP(#2 t, remove_specials t1, remove_specials t2)
    end
  | ABS(v, t2) => Absyn.LAM(#2 t, to_vabsyn v, remove_specials t2)
  | TYPED(t, (ty,_)) => Absyn.TYPED(#2 t, remove_specials t, ty)
  | VAR s => Absyn.IDENT(#2 t, s)
  | QIDENT(x,y) => Absyn.QIDENT(#2 t, x, y)
  | AQ x => Absyn.AQ(#2 t, x)
and remove_recupdate locn upd1 updates bottom = let
  open Absyn
in
  case #1 upd1 of
    COMB((COMB((VAR s,slocn), (VAR fld,_)),sflocn), newvalue) => let
    in
      if s = recfupd_special then
        APP(locn, APP(#2 upd1, IDENT (sflocn,s^fld), remove_specials newvalue),
            remove_recupdate' (#2 updates) updates bottom)
      else if s = recupd_special then
        APP(locn, APP(#2 upd1, IDENT (sflocn, recfupd_special^fld),
                      APP(locn.Loc_None, QIDENT(locn.Loc_None, "combin", "K"),
                          remove_specials newvalue)),
            remove_recupdate' (#2 updates) updates bottom)
      else raise ParseTermError (recupd_errstring,slocn)
    end
  | _ =>
    raise ParseTermError (recupd_errstring,#2 upd1)
end
and remove_recupdate' locn updatelist bottom = let
  open Absyn
in
  case #1 updatelist of
    VAR s => if s = recnil_special then bottom
             else raise ParseTermError (recupd_errstring,#2 updatelist)
  | COMB((COMB((VAR s,slocn), upd1),sflocn), updates) => let
    in
      if s = reccons_special then remove_recupdate locn upd1 updates bottom
      else
        if s = recupd_special orelse s = recfupd_special then
          case #1 upd1 of
            VAR fldname =>
            if s = recfupd_special then
              APP(locn,APP(#2 upd1, IDENT (sflocn,s^fldname),
                           remove_specials updates),
                  bottom)
            else
              APP(locn,APP(#2 upd1, IDENT (sflocn, recfupd_special^fldname),
                           APP(locn.Loc_None,
                               QIDENT(locn.Loc_None, "combin", "K"),
                               remove_specials updates)),
                  bottom)
          | _ => raise ParseTermError
              ("Must have field name as first argument to update operator",#2 upd1)
        else
          raise ParseTermError (recupd_errstring,slocn)
    end
  | _ => raise ParseTermError (recupd_errstring,#2 updatelist)
end


fun top_nonterminal pstack =
  case pstack of
    PStack {stack = ((NonTerminal pt,locn), _)::_, ...} => remove_specials (pt,locn)
  | PStack {stack = ((_,locn),_)::_, ...} =>
      raise ParseTermError ("No non-terminal on top of stack",locn)
  | _ =>
      raise ParseTermError ("No non-terminal on top of stack",locn.Loc_Unknown(*TODO*))

(*
infix Gmerge


Useful functions to test with:
fun do_parse0 G ty = let
  val pt = parse_term G ty
in
  fn q => let
    val ((cs, p), _) = pt (q, PStack {lookahead = [], stack = [],
                                      in_vstruct = false})
  in
    case pstack p of
      [(NonTerminal pt, _), (Terminal BOS, _)] => remove_specials pt
    | _ => raise Fail "Parse failed "
  end
end

Remember to start with
  quotation := true
in raw MoscowML sessions

fun pp (v : ''a) = let
  val p:''a frag list -> ''a preterm =
    do_parse0 stdhol (parse_type.parse_type parse_type.empty_grammar)
in
  p
end

fun ppt (v: ''a) = let
  fun fix_stack stack =
    case stack of
      ((NonTerminal t, _)::rest) =>
        pop >> push (NonTerminal(remove_specials t), XXX)
    | x => ok
  val p:''a frag list -> ((''a frag list * ''a PStack) * unit option) =
    fn q =>
    (parse_term stdhol (parse_type.parse_type parse_type.empty_grammar) >>
     getstack >- fix_stack)
    (q, PStack{lookahead = [], stack = [], in_vstruct = false})
in
  p
end

val p = pp ()
*)
(*
quotation := true;
val pType = parse_type.pType
fun do_test (q, res) = let
  val test = p q
in
  if test <> res then let
  in
    print "Failure on: \"";
    print (quotetoString q);
    print "\" not parsing to ";
    Meta.printVal res;
    print "\n"
  end else ()
end handle _ => print ("Failure of \""^quotetoString q^"\" to parse at all\n");

val tests : (unit frag list * unit preterm) list =
[(`x`,              VAR "x"),
 (`x'`,             VAR "x'"),
 (`f x`,            COMB (VAR "f", VAR "x")),
 (`f x y` ,         COMB (COMB (VAR "f", VAR "x"), VAR "y")),
 (`p /\ q`,         COMB (COMB (VAR "/\\", VAR "p"), VAR "q")),
 (`p /\ q \/ r`,    COMB (COMB(VAR "\\/", COMB(COMB(VAR "/\\", VAR "p"),
                                               VAR "q")),
                          VAR "r")),
 (`f : num`,        TYPED(VAR "f", parse_type.pType("num", []))),
 (`f x : bool list`,TYPED(COMB(VAR "f", VAR "x"),
                          pType("list", [pType("bool", [])]))),
 (`f (p \/ q)`,     COMB(VAR "f", COMB (COMB (VAR "\\/", VAR "p"), VAR "q"))),
 (`f ^(())`,        COMB(VAR "f", AQ ())),
 (`f (p:bool \/ q)`,COMB(VAR "f",
                         COMB(COMB(VAR "\\/",
                                   TYPED(VAR "p", pType("bool", []))),
                              VAR "q"))),
 (`f x.f1`,         COMB(VAR "f", COMB(COMB(VAR rec_special, VAR "x"),
                                       VAR "f1"))),
 (`f theni`,        COMB(VAR "f", VAR "theni")),
 (`\x. x`,          ABS (SIMPLE "x", VAR "x")),
 (`\x y. x`,        ABS (SIMPLE "x", ABS (SIMPLE "y", VAR "x"))),
 (`?x y. x`,        COMB (VAR "?", ABS (SIMPLE "x",
                                        COMB(VAR "?",
                                             ABS(SIMPLE "y", VAR "x"))))),
 (`[p; q]`,         COMB (COMB(VAR "CONS", VAR "p"),
                          COMB(COMB(VAR "CONS", VAR "q"), VAR "NIL"))),
 (`f [] x`,         COMB (COMB (VAR "f", VAR "NIL"), VAR "x")),
 (`[[]]`,           COMB (COMB (VAR "CONS", VAR "NIL"), VAR "NIL")),
 (`\^(()). x`,      ABS(VS_AQ(), VAR "x")),
 (`f x = if ~f p /\ t then q else r`,
                    COMB(COMB(VAR "=", COMB(VAR "f", VAR "x")),
                         COMB(COMB(COMB(VAR "COND",
                                        COMB(COMB(VAR "/\\",
                                                  COMB(VAR "~",
                                                       COMB(VAR "f",VAR "p"))),
                                             VAR "t")),
                                   VAR "q"),
                              VAR "r")))];



app do_test tests;

*)


end
