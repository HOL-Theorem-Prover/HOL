structure parse_term :> parse_term =
struct

open Lib
open monadic_parse optmonad term_tokens term_grammar HOLgrammars
open GrammarSpecials
infix >> >- ++ >->

val WARN = Feedback.HOL_WARNING "parse_term";


exception ParseTermError of string
type 'a token = 'a term_tokens.term_token

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
  | VPAIR of ('a varstruct * 'a varstruct)
  | TYPEDV of 'a varstruct * Pretype.pretype
  | RESTYPEDV of 'a varstruct * 'a preterm
  | VS_AQ of 'a
and 'a preterm
  = COMB of ('a preterm * 'a preterm)
  | VAR of string
  | QIDENT of string * string
  | ABS of ('a varstruct * 'a preterm)
  | AQ of 'a
  | TYPED of ('a preterm * Pretype.pretype)

fun strip_comb0 acc (COMB(t1, t2)) = strip_comb0 (t2::acc) t1
  | strip_comb0 acc t = (t, acc)
fun strip_comb t = strip_comb0 [] t

fun list_mk_comb (t, []) = t
  | list_mk_comb (t, (x::xs)) = list_mk_comb(COMB(t,x), xs)

(* checks that there are never two adjacent TM elements and further that
   no TM element is either the first or last element of the list *)
(* also disallows the empty list *)
fun e_list_ok [] = false
  | e_list_ok [TOK _] = true
  | e_list_ok (TM :: _) = false
  | e_list_ok (TOK _::(rest as (TOK _ :: _))) = e_list_ok rest
  | e_list_ok (TOK _:: TM :: rest) = e_list_ok rest

fun apply_flist [] x = x
  | apply_flist (f::fs) x = apply_flist fs (f x)

fun CCOMB(x,y) = COMB(y,x)

infix --
fun (l1 -- []) = l1
  | (l1 -- (x::xs)) = List.filter (fn y => y <> x) l1 -- xs

fun all_tokens strlist =
  map STD_HOL_TOK strlist @ [BOS, EOS, Id, TypeColon, TypeTok, EndBinding]

exception PrecConflict of stack_terminal * stack_terminal

val complained_already = ref false;


fun mk_prec_matrix G = let
  exception NotFound
  exception BadTokList
  val {lambda, endbinding, type_intro, restr_binders, ...} = specials G
  val specs = grammar_tokens G
  val Grules = term_grammar.grammar_rules G
  val alltoks =
    ResquanOpTok :: VS_cons :: STD_HOL_TOK fnapp_special :: all_tokens specs
  val matrix:(stack_terminal * stack_terminal, order) Polyhash.hash_table =
    Polyhash.mkPolyTable (length specs * length specs, NotFound)
  val rule_elements = term_grammar.rule_elements o #elements
  val complained_this_iteration = ref false
  fun insert k v = let
    val insert_result = Polyhash.peekInsert matrix (k, v)
  in
    case (insert_result, v) of
      (SOME EQUAL, _) => ()  (* ignore this *)
    | (SOME _, EQUAL) => Polyhash.insert matrix (k,v)  (* EQUAL overrides *)
    | (SOME oldv, _) => if oldv <> v then
                          (Polyhash.insert matrix (k, LESS);
                           complained_this_iteration := true;
                           if not (!complained_already) then
                             (Feedback.HOL_WARNING
                                "Parse" "Term"
                                ("Grammar ambiguous on token pair "^
                                 STtoString G (#1 k) ^ " and " ^
                                 STtoString G (#2 k) ^ ", and "^
                                 "probably others too");
                              complained_already := true)
                           else
                              ())
                        else ()
    | (NONE, _) => ()
  end
  fun insert_eqs rule = let
    fun insert_oplist list = let
      val toks = List.mapPartial (fn TOK s => SOME s | _ => NONE) list
      fun recurse [] = raise BadTokList
        | recurse [x] = ()
        | recurse (x::(xs as y::_)) = let
          in
            insert (STD_HOL_TOK x, STD_HOL_TOK y) EQUAL;
            recurse xs
          end
    in
      recurse toks
    end
  in
    case rule of
      PREFIX (STD_prefix rules) => app (insert_oplist o rule_elements) rules
    | PREFIX (BINDER slist) =>
        app (fn b => insert (STD_HOL_TOK (binder_to_string G b),
                             EndBinding) EQUAL) slist
    | SUFFIX (STD_suffix rules) => app (insert_oplist o rule_elements) rules
    | SUFFIX TYPE_annotation => ()
    | INFIX (STD_infix (rules, _)) => app (insert_oplist o rule_elements) rules
    | INFIX RESQUAN_OP => ()
    | CLOSEFIX rules => app (insert_oplist o rule_elements) rules
    | LISTRULE rlist => let
        fun process r = let
          val left = STD_HOL_TOK (#leftdelim r)
          val right = STD_HOL_TOK (#rightdelim r)
          val separator = STD_HOL_TOK (#separator r)
        in
          insert (left, right) EQUAL;
          insert (left, separator) EQUAL;
          insert (separator, separator) EQUAL;
          insert (separator, right) EQUAL
        end
      in
        app process rlist
      end
    | FNAPP => ()
    | VSCONS => ()
  end

  (* the right hand end of a suffix or a closefix is greater than
     everything *)
  val closed_rhses = find_suffix_rhses G
  fun insert_rhs_relns () = let
    val all = alltoks
    val rhses = closed_rhses
  in
    app (fn rhs => app (fn t => insert (rhs, t) GREATER) all) rhses
  end

  (* everything not a suffix rhs is less than the left hand end of a
     prefix/closefix *)
  val closed_lhses = find_prefix_lhses G
  fun insert_lhs_relns () = let
    val all = alltoks -- (EOS::closed_rhses)
  in
    app (fn lhs => app (fn t => insert (t, lhs) LESS) all) closed_lhses
  end
  fun map_rule f [] = []
    | map_rule f (x::xs) = let
        val rest = map_rule f xs
        val here =
          case x of
            INFIX (STD_infix (rules, _)) => map (f o rule_elements) rules
          | SUFFIX (STD_suffix rules) => map (f o rule_elements) rules
          | PREFIX (STD_prefix rules) => map (f o rule_elements) rules
          | CLOSEFIX rules => map (f o rule_elements) rules
          | LISTRULE rlist => let
              fun process r =
                [f (map TOK [#leftdelim r, #separator r, #rightdelim r])]
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
    List.mapPartial (fn (k,v) => if v = EQUAL then SOME k else NONE)
    (Polyhash.listItems matrix)
  fun terms_between_equals (k1, k2) = let
  in
    app (fn lhs => insert (k1, lhs) LESS) all_lhs;
    app (fn rhs => insert (rhs, k2) GREATER) all_rhs
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
  fun rule_left (rr: rule_record) =
    case hd (rule_elements rr) of
      TOK s => STD_HOL_TOK s
    | _ => raise Fail ("rule list is bogus for "^ #term_name rr)
  fun rule_right (rr:rule_record) =
    case List.last (rule_elements rr) of
      TOK s => STD_HOL_TOK s
      | _ => raise Fail ("rule list is bogus for "^ #term_name rr)
  fun right_grabbing_elements rule =
    case rule of
      INFIX(STD_infix(rules, _)) => map rule_right rules
    | INFIX RESQUAN_OP => [ResquanOpTok]
    | PREFIX (BINDER _) => [EndBinding]
    | PREFIX (STD_prefix rules) => map rule_right rules
    | FNAPP => [STD_HOL_TOK fnapp_special]
    | VSCONS => [VS_cons]
    | _ => []
  fun left_grabbing_elements rule =
    case rule of
      INFIX (STD_infix(rules, _)) => map rule_left rules
    | INFIX RESQUAN_OP => [ResquanOpTok]
    | SUFFIX (STD_suffix rules) => map rule_left rules
    | SUFFIX TYPE_annotation => [TypeColon]
    | FNAPP => [STD_HOL_TOK fnapp_special]
    | VSCONS => [VS_cons]
    | _ => []
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
             (fn lower_right => insert (lower_right, lefttok) GREATER)
             lower_rights)
        this_level_lefts;
        app (fn righttok =>
             app
             (fn lower_left => insert (righttok, lower_left) LESS)
             lower_lefts)
        this_level_rights;
        case assoc of
          LEFT => let
          in
            app (fn right_tok =>
                 app (fn left_tok => insert (right_tok, left_tok) GREATER)
                 this_level_lefts)
            this_level_rights
          end
        | RIGHT => let
          in
            app (fn right_tok =>
                 app (fn left_tok => insert (right_tok, left_tok) LESS)
                 this_level_lefts)
            this_level_rights
          end
        | NONASSOC => ()
      end
    | INFIX RESQUAN_OP => let
        val lower_rights = List.concat (map right_grabbing_elements remainder)
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
      in
        app (fn lower_right => insert(lower_right, ResquanOpTok) GREATER)
        lower_rights;
        app (fn lower_left => insert(ResquanOpTok, lower_left) LESS)
        lower_lefts
      end
    | PREFIX (STD_prefix rules) => let
        val this_level_rights = map rule_right rules
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
      in
        app (fn right_tok =>
             app
             (fn lower_left => insert (right_tok, lower_left) LESS)
             lower_lefts)
        this_level_rights
      end
    | PREFIX (BINDER s) => let
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
      in
        app (fn lower_left => insert (EndBinding, lower_left) LESS) lower_lefts
      end
    | SUFFIX TYPE_annotation => let
        val lower_rights = List.concat (map right_grabbing_elements remainder)
      in
        app (fn lower_right => insert (lower_right, TypeColon) GREATER)
        lower_rights
      end
    | SUFFIX (STD_suffix rules) => let
        val lower_rights = List.concat (map right_grabbing_elements remainder)
        val lefts = map rule_left rules
      in
        app (fn left_tok =>
             app (fn lower_right => insert (lower_right, left_tok) GREATER)
             lower_rights)
        lefts
      end
    | FNAPP => let
        val lower_rights = List.concat (map right_grabbing_elements remainder)
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
        val fnapp = STD_HOL_TOK fnapp_special
      in
        app (fn lower_left => insert (fnapp, lower_left) LESS) lower_lefts;
        app (fn lower_right => insert (lower_right, fnapp) GREATER)
        lower_rights;
         (* function application left associative *)
        insert (fnapp, fnapp) GREATER
      end
    | VSCONS => let
        val lower_rights = List.concat (map right_grabbing_elements remainder)
        val lower_lefts = List.concat (map left_grabbing_elements remainder)
      in
        app (fn lower_left => insert (VS_cons, lower_left) LESS) lower_lefts;
        app (fn lower_right => insert (lower_right, VS_cons) GREATER)
        lower_rights;
        insert (VS_cons, VS_cons) EQUAL
      end
    | _ => ()
  fun apply_them_all f [] = ()
    | apply_them_all f (x::xs) = (f x xs ; apply_them_all f xs)
in
  app insert_eqs Grules ;
  insert (BOS, EOS) EQUAL;
  insert (STD_HOL_TOK lambda, EndBinding) EQUAL;
  app terms_between_equals (calc_eqpairs());
  (* these next equality pairs will never have terms interfering between
     them, so we can insert the equality relation between them after doing
     the above *)
  insert (TypeColon, TypeTok) EQUAL;
  app (fn b => insert (STD_HOL_TOK b, EndBinding) EQUAL) (binders G);
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
  val table:(rule_element list, rule_summary)Polyhash.hash_table =
       Polyhash.mkPolyTable (2 * length Grules, Fail "")
  fun insert_rule f g rr =
    Polyhash.insert table (g (term_grammar.rule_elements (#elements rr)),
                           f (#term_name rr))
  fun infix_f elms = elms @ [TM]
  fun suffix_f elms = elms
  fun closefix_f elms = elms
  fun prefix_f elms = elms @ [TM]
  fun addrule rule =
    case rule of
      INFIX (STD_infix(rules, _)) => app (insert_rule infix_rule infix_f) rules
    | INFIX RESQUAN_OP => ()
    | PREFIX (STD_prefix rules) => app (insert_rule prefix_rule prefix_f) rules
    | PREFIX (BINDER s) => ()
    | SUFFIX (STD_suffix rules) => app (insert_rule suffix_rule suffix_f) rules
    | SUFFIX TYPE_annotation => ()
    | CLOSEFIX rules => app (insert_rule closefix_rule closefix_f) rules
    | FNAPP => Polyhash.insert table (infix_f [TOK fnapp_special],
                                      infix_rule fnapp_special)
    | VSCONS => ()
    | LISTRULE rlist => let
        fun process r = let
          val nil_pattern = [TOK (#leftdelim r), TOK (#rightdelim r)]
          val singleton_pat = [TOK (#leftdelim r), TM, TOK (#rightdelim r)]
          val doubleton_pat = [TOK (#leftdelim r), TM, TOK (#separator r),
                               TM, TOK (#rightdelim r)]
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


fun lift (P : ('a, 'b) Parser) (x:'b list * 'c) = let
  val (newx1, result) = P (#1 x)
in
  ((newx1, #2 x), result)
end

fun mwhile B C =
  B >-  (fn b => if b then C >> mwhile B C else ok)

fun mif B C = B >- (fn b => if b then C else ok)

datatype 'a stack_item =
  Terminal of stack_terminal |
  NonTerminal of 'a preterm |
  NonTermVS of 'a varstruct list

fun is_terminal (Terminal _) = true
  | is_terminal _ = false
fun dest_terminal (Terminal x) = x
  | dest_terminal _ = raise Fail "dest_terminal not called on terminal"
fun is_nonterm t = not (is_terminal t)


datatype 'a lookahead_item =
  Token of 'a term_token | PreType of Pretype.pretype |
  LA_Symbol of stack_terminal

datatype vsres_state = VSRES_Normal | VSRES_VS | VSRES_RESTM

datatype 'a PStack =
  PStack of {stack : ('a stack_item * 'a lookahead_item) list,
             lookahead : 'a lookahead_item list,
             in_vstruct : (vsres_state * int) list}



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

fun invstructp (cs, p) = ((cs, p), SOME (invstructp0 p))

fun inc_paren (cs, p) = ((cs, fupd_vs0 (fupd_hd (fupd_snd (fn n => n + 1))) p),
                         SOME ())
fun dec_paren (cs, p) = ((cs, fupd_vs0 (fupd_hd (fupd_snd (fn n => n - 1))) p),
                         SOME ())
fun enter_binder (cs,p) =
  ((cs, fupd_vs0 (fn rest => (VSRES_VS, 0)::rest) p), SOME ())
fun enter_restm (cs, p) =
  ((cs, fupd_vs0 (fupd_hd (fupd_fst (K VSRES_RESTM))) p), SOME ())
fun leave_restm (cs, p) =
  ((cs, fupd_vs0 (fupd_hd (fupd_fst (K VSRES_VS))) p), SOME ())
fun leave_binder (cs, p) = ((cs, fupd_vs0 tl p), SOME ())

fun push_pstack p i = upd_stack p (i::pstack p)
fun top_pstack p = hd (pstack p)
fun pop_pstack p = upd_stack p (tl (pstack p))

fun push t (cs, p) = ((cs, push_pstack p t), SOME ())
fun topterm (cs, p) =
  ((cs, p), List.find (is_terminal o #1) (pstack p))
fun pop (cs, p) = ((cs, pop_pstack p), SOME (top_pstack p))
fun getstack (cs, p) = ((cs, p), SOME (pstack p))


fun set_la tt (cs, p) = ((cs, upd_la p tt), SOME ())
fun current_la (cs, p) = ((cs, p), SOME (pla p))

fun findpos P [] = NONE
  | findpos P (x::xs) = if P x then SOME(0,x)
                        else Option.map (fn (n,x) => (n + 1, x)) (findpos P xs)

fun parse_term (G : grammar) typeparser = let
  val Grules = grammar_rules G
  val {type_intro, lambda, endbinding, restr_binders, res_quanop} = specials G
  val num_info = numeral_info G
  val overload_info = overload_info G
  val closed_lefts = find_prefix_lhses G
  val ty_annote_prec = let
    val ty_annote =
      findpos (fn (SUFFIX TYPE_annotation) => true | _ => false) Grules
  in
    #1 (valOf ty_annote)
  end handle Option => raise Fail "Grammar must allow type annotation"
  val prec_matrix = mk_prec_matrix G
  val rule_db = mk_ruledb G
  val is_binder = is_binder G
  val grammar_tokens = term_grammar.grammar_tokens G
  val lex = lift (term_tokens.lex (endbinding::grammar_tokens))
  val keyword_table = Polyhash.mkPolyTable (50, Fail "")
  val _ = app (fn v => Polyhash.insert keyword_table (v, ())) grammar_tokens
  fun itemP P = lex >- (fn t => if P t then return t else fail)
  fun item t = itemP (fn t' => t = t')

  fun transform (in_vs as (vs_state, nparens)) (t:'a lookahead_item option) =
    case t of
      NONE => (EOS, t)
    | SOME (Token x) => let
      in
        case x of
          Ident s =>
            if String.sub(s,0) = #"$" then
              (Id, SOME (Token (Ident (String.extract(s,1,NONE)))))
            else if s = res_quanop andalso vs_state = VSRES_VS then
              (ResquanOpTok, t)
            else if s = type_intro then (TypeColon, t)
            else if s = vs_cons_special then (VS_cons, t)
            else if s = endbinding andalso nparens = 0 andalso
              vs_state <> VSRES_Normal then (EndBinding, t)
            else if isSome (Polyhash.peek keyword_table s) then
              (STD_HOL_TOK s, t)
            else (Id, t)
        | Antiquote _ => (Id, t)
        | Numeral _ => (Id, t)
        | QIdent _ => (Id, t)
      end
    | SOME (PreType ty) => (TypeTok, t)
    | SOME (LA_Symbol st) => (st, t)

  (* find the initial segment of the stack such that all of the segment
     has the equality relation between components and such that the first
     element not in the segment is less than than the last one in the
     segment *)
  fun find_reduction stack =
    case stack of
      [] => raise Fail "find_reduction: stack empty!"
    | [_] => raise Fail "find_reduction: stack singleton!"
    | ((t1 as (Terminal x1, _))::rest) => let
      in
        case rest of
          [] => raise Fail "find_reduction : impossible"
        | ((Terminal x2, _)::_) => let
            val res = valOf (Polyhash.peek prec_matrix (x2,x1))
              handle Option =>
                raise Fail ("No relation between "^STtoString G x2^" and "^
                            STtoString G x1);
          in
            case res of
              LESS => [t1]
            | EQUAL =>  (t1::find_reduction rest)
            | GREATER => raise Fail "find_reduction: found a greater on stack"
          end
        | (t2::rest2) => let
            (* t2 is a non-terminal, whether VS or not *)
          in
            case rest2 of
              [] => raise Fail "find_reduction : nonterminal at stack base!"
            | ((Terminal x2, _)::_) => let
                val res = valOf (Polyhash.peek prec_matrix (x2, x1))
                  handle Option =>
                    raise Fail ("No relation between "^STtoString G x2^" and "^
                                STtoString G x1)
              in
                case res of
                  LESS => [t1,t2]
                | EQUAL => t1::t2::find_reduction rest2
                | GREATER => raise Fail "find_reduction: greater on stack!"
              end
            | (_::_) => raise Fail "find_reduction 2 NTs!"
          end
      end
    | (t1::rest) => t1::find_reduction rest (* t1 a non-terminal *)

  (* given an initial segment of the stack that corresponds to a reduction,
     determine whether or not this corresponds to a rule, and if it does
     pull the tokens of the stack and replace them with the right
     non-terminal *)
  fun perform_reduction rhs = let
    fun ok_item (Terminal (STD_HOL_TOK _), _) = true
      | ok_item (NonTerminal _, _) = true
      | ok_item _ = false

    (* what follows is only called on what will be list RHSes of
     length greater than two, as smaller lists will have been caught
     by the insertion of these rules specifically into the DB. *)

    fun handle_list_reduction rhs = let
      exception Hah
      fun possible_list pattern = let
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
      fun stack_item_to_rule_element (Terminal (STD_HOL_TOK s)) = TOK s
        | stack_item_to_rule_element (NonTerminal _) = TM
        | stack_item_to_rule_element _ = raise Fail "perform_reduction: gak!"
      val rhs = List.rev rhs
      val translated_rhs0 = map (stack_item_to_rule_element o #1) rhs
      val (translated_rhs, top_was_tm) =
        case translated_rhs0 of
          (TM::rest) => (rest, true)
        | _ => (translated_rhs0, false)
      val rule = valOf (Polyhash.peek rule_db translated_rhs)
        handle Option => let
          val errmsg = "No rule for "^listtoString reltoString translated_rhs
        in
          valOf (handle_list_reduction translated_rhs)
          handle Option => raise Fail errmsg
        end
      val _ =
        case rule of
          infix_rule s => top_was_tm orelse
            raise Fail ("missing left argument to "^s)
        | suffix_rule s => top_was_tm orelse
              raise Fail ("missing first argument to "^s)
        | _ => true
      fun item_to_pterm (NonTerminal p, _) = SOME p
        | item_to_pterm _ = NONE
      val lrhs = length rhs
      val mapP = List.mapPartial
      val n = if top_was_tm then 1 else 0
      val (numtopop, newterm) =
        case rule of
          listfix_rule r => let
            val args = mapP item_to_pterm rhs
            fun mk_list [] = VAR (#nilstr r)
              | mk_list (x::xs) = COMB(COMB(VAR (#cons r), x), mk_list xs)
          in
            (lrhs - n, mk_list args)
          end
        | _ => let
            val (args, numtopop, head) =
              case rule of
                infix_rule s => (mapP item_to_pterm rhs, lrhs, s)
              | prefix_rule s => (mapP item_to_pterm (tl rhs), lrhs - n, s)
              | suffix_rule s => (mapP item_to_pterm rhs, lrhs, s)
              | closefix_rule s => (mapP item_to_pterm (tl rhs), lrhs - n, s)
              | _ => raise Fail "parse_term : can't happen"
          in
            (numtopop, List.foldl CCOMB (VAR head) args)
          end
    in
      repeatn numtopop pop >> push (NonTerminal newterm, Token (Ident "XXX"))
    end
  else
    case rhs of
      ((Terminal Id, tt as Token (Antiquote a))::_) => let
      in
        pop >> invstructp >-
        (fn inv =>
         if #1 (hd inv) = VSRES_VS then
           push (NonTermVS [VS_AQ a], tt)
         else
           push (NonTerminal (AQ a), tt))
      end
    | ((Terminal Id, Token tt)::_) => let
        exception Temp
      in
        pop >> invstructp >-
        (fn inv => let
          val thing_to_push =
            case (#1 (hd inv), tt) of
              (VSRES_VS, Numeral _) => let
              in
                WARN "term_parser" "can't have numerals in binding positions";
                raise Temp
              end
            | (_, Numeral(dp, copt)) => let
                val numeral_part =
                  Literal.gen_mk_numeral
                       {mk_comb = COMB,
                        ZERO = QIDENT ("num", "0"),
                        ALT_ZERO = QIDENT ("arithmetic", "ALT_ZERO"),
                        NUMERAL  = QIDENT ("arithmetic", "NUMERAL"),
                        BIT1     = QIDENT ("arithmetic", "NUMERAL_BIT1"),
                        BIT2     = QIDENT ("arithmetic", "NUMERAL_BIT2")}
                    (Arbnum.fromString dp)
                fun inject_np NONE = numeral_part
                  | inject_np (SOME s) = COMB(VAR s, numeral_part)
              in
                case copt of
                  SOME c => let
                    val injector = List.find (fn (k,v) => k = c) num_info
                  in
                    case injector of
                      NONE => let
                      in
                        WARN "term_parser"
                         ("Invalid suffix "^str c^ " for numeral");
                        raise Temp
                      end
                    | SOME (_, strop) => NonTerminal (inject_np strop)
                  end
                | NONE =>
                  if null num_info then
                    if dp = "0" then
                      (WARN "term_parser"
                       ("\n   0 treated specially and allowed - "^
                        "no other numerals permitted");
                      NonTerminal (inject_np NONE))
                    else
                      (WARN "term_parser"  "No numerals currently allowed";
                       raise Temp)
                  else let
                    val fns = fromNum_str
                  in
                    if Overload.is_overloaded overload_info fns then
                      NonTerminal (inject_np (SOME fns))
                    else
                      (WARN "term_parser"
                       ("No overloadings exist for "^fns^
                        ": use character suffix for numerals");
                       raise Temp)
                      (* NonTerminal (inject_np (#2 (hd num_info))) *)
                  end
              end
            | (VSRES_VS, _) => NonTermVS [SIMPLE (token_string tt)]
            | (_, QIdent x) => NonTerminal (QIDENT x)
            | _ => NonTerminal (VAR (token_string tt))
              (* tt is not an antiquote because of the wider context;
                 antiquotes are dealt with in the wider case statement
                 above *)
        in
           push (thing_to_push, Token tt)
        end handle Temp => fail)
      end
    | ((Terminal TypeTok, PreType ty)::(Terminal TypeColon, _)::
       (NonTerminal t, _)::rest) => let
      in
        repeatn 3 pop >> push (NonTerminal (TYPED (t, ty)),
                               Token (Ident "XXX"))
      end
    | ((Terminal TypeTok, PreType ty)::(Terminal TypeColon, _)::
       (NonTermVS vsl, _)::rest) => let
       in
         repeatn 3 pop >> push (NonTermVS (map (fn v => TYPEDV(v,ty)) vsl),
                                Token (Ident "XXX"))
       end
    | ((NonTerminal t, _)::(Terminal EndBinding, _)::
       (NonTermVS vsl, _)::(Terminal (STD_HOL_TOK binder), _)::rest) => let
       exception Urk of string in let
        fun has_resq v =
          case v of
            VPAIR(v1,v2) => has_resq v1 orelse has_resq v2
          | TYPEDV(v0, ty) => has_resq v0
          | RESTYPEDV _ => true
          | _ => false
        fun has_tupled_resq (VPAIR(v1, v2)) = has_resq v1 orelse has_resq v2
          | has_tupled_resq (TYPEDV(v0, _)) = has_tupled_resq v0
          | has_tupled_resq (RESTYPEDV(v0, _)) = has_tupled_resq v0
          | has_tupled_resq _ = false
        fun ERROR s1 s2 = Urk (s1^": "^s2)
        fun extract_resq v =
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
        fun comb_abs_fn(v,t) =
          if has_tupled_resq v then
            raise ERROR "parse_term"
              "Can't have restricted quantification on nested arguments"
          else
            case extract_resq v of
              NONE => COMB(VAR binder, ABS(v, t))
            | SOME (v',P) =>
                COMB(COMB(VAR (Lib.assoc (BinderString binder) restr_binders),
                          P),
                     ABS(v', t))
                handle Feedback.HOL_ERR _ =>
                  raise ERROR "parse_term"
                    ("No restricted quantifier associated with "^binder)
        fun abs_fn (v,t) =
          if has_tupled_resq v then
            raise ERROR "parse_term"
              "Can't have restricted quantification on nested arguments"
          else
            case extract_resq v of
              NONE => ABS(v,t)
            | SOME(v', P) =>
                COMB(COMB(VAR (Lib.assoc LAMBDA restr_binders), P), ABS(v', t))
                handle Feedback.HOL_ERR _ =>
                  raise ERROR "parse_term"
                    "No restricted quantifier associated with lambda"
        val vsl = List.rev vsl
        val abs_t =
          List.foldr (if binder = lambda then abs_fn else comb_abs_fn) t vsl
      in
        repeatn 4 pop >> push (NonTerminal abs_t, Token (Ident "XXX"))
      end handle Urk s => (print (s^"\n"); fail) end
    | ((Terminal(STD_HOL_TOK ")"), _)::(vsl as (NonTermVS _,_))::
       (Terminal(STD_HOL_TOK "("), _)::rest) => let
      in
        repeatn 3 pop >> push vsl
      end
    | ((NonTermVS vsl1, _)::(Terminal(STD_HOL_TOK ","), _)::
       (NonTermVS vsl2, _)::rest) => let
       in
         if length vsl1 <> 1 orelse length vsl2 <> 1 then
           (print "Can't have lists of atoms as arguments to , in binder";
            fail)
           else
             repeatn 3 pop >> push (NonTermVS [VPAIR(hd vsl2, hd vsl1)],
                                    Token (Ident "XXX"))
       end
    | ((NonTerminal t, _)::(Terminal ResquanOpTok, _)::
       (NonTermVS vsl, _)::rest) => let
      in
         repeatn 3 pop >> push (NonTermVS (map (fn v => RESTYPEDV(v,t)) vsl),
                                Token (Ident "XXX")) >>
         leave_restm
      end
    | _ => let
      fun is_vcons_list [] = false
        | is_vcons_list [x] = false
        | is_vcons_list ((NonTermVS _, _)::(Terminal VS_cons, _)::rest) = let
          in
            case rest of
              [(NonTermVS _,_)] => true
            | _ => is_vcons_list rest
          end
        | is_vcons_list _ = false
      fun get_vsls (NonTermVS vsl, _) = SOME vsl | get_vsls _ = NONE
    in
      if is_vcons_list rhs then
        repeatn (length rhs) pop >>
        push (NonTermVS(List.concat (List.mapPartial get_vsls rhs)),
              Token(Ident "XXX"))
      else
        (print "Can't do this sort of reduction\n"; fail)
    end
  end handle Fail s => (print s; print "\n"; fail)


  val do_reduction =
    getstack >- (return o find_reduction) >- perform_reduction


  fun el2list x = [x]
  (* calls the lexer and puts the result onto the lookahead list *)
  val get_item = (lex >- set_la o el2list o Token) ++ (set_la [])

  (* takes the top (first) terminal from the lookahead list (there is
     assumed to be one), and transfers it to the stack.  If this
     empties the lookahead list, then this is replenished by calling
     the appropriate lexer *)

  val shift =
    current_la >-
    (fn la => invstructp >- (return o hd) >-
     (fn in_vs =>
      case la of
        [] => fail
      | (x0::xs) => let
          val (terminal,x) = transform in_vs (SOME x0)
        in
          push (Terminal terminal, valOf x) >>
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
    val (input_term, _) = transform (hd in_vs) tt
    val top = dest_terminal top_item
    val ttt = Terminal input_term
    fun less_action stack =
      (* if the next thing in the lookahead might begin a whole new phrase,
         i.e. is a closed lhs, and the top thing on the stack is a non-terminal
         then we should insert the magical function application operator *)
      case stack of
        (NonTerminal _, _)::_ => let
          val fnt = LA_Symbol (STD_HOL_TOK fnapp_special)
        in
          if mem input_term closed_lefts then
            current_la >- (fn oldla => set_la (fnt::oldla))
          else
            shift
        end
      | (NonTermVS _, _) :: _ => let
          val fnt = LA_Symbol VS_cons
        in
          if mem input_term closed_lefts then
            current_la >- (fn oldla => set_la (fnt::oldla))
          else
            shift
        end
      | _ => shift
    val usual_action =
      case Polyhash.peek prec_matrix (top, input_term) of
        NONE => let
        in
          print ("Don't expect to find a "^STtoString G input_term^" in this "^
                 "position after a "^STtoString G top^"\n");
          fail
        end
      | SOME order => let
        in
          case order of
            LESS => getstack >- less_action
          | EQUAL => shift
          | GREATER => do_reduction
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
            [x] =>
              lift typeparser >-  (fn ty => set_la [x, PreType ty])
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
  push (Terminal BOS, Token (Ident "XXX")) >> get_item >>
  mwhile (current_input >-
          (fn optt => if (isSome optt) then return true
                      else
                        (topterm >- (fn t => return (#1 t <> Terminal BOS)))))
  basic_action
end

val initial_pstack = PStack {stack = [], lookahead = [],
                             in_vstruct = [(VSRES_Normal, 0)]}

fun is_final_pstack p =
  case p of
    PStack {stack = [(NonTerminal pt, _), (Terminal BOS, _)],
            lookahead = [], in_vstruct = [(VSRES_Normal, 0)]} => true
  | _ => false

val recupd_errstring =
  "Record list must have (fld := value) or (fld updated_by f) elements only"

fun to_vabsyn vs =
  case vs of
    SIMPLE x => Absyn.VIDENT x
  | VPAIR(v1,v2) => Absyn.VPAIR(to_vabsyn v1, to_vabsyn v2)
  | TYPEDV(v,ty) => Absyn.VTYPED(to_vabsyn v, ty)
  | VS_AQ x => Absyn.VAQ x
  | RESTYPEDV _ =>
      raise ParseTermError
        "Attempt to convert a vstruct still containing a RESTYPEDV"

fun remove_specials t =
  case t of
    COMB (t1, t2) => let
      open Absyn
    in
      case t1 of
        VAR s => if s = bracket_special then remove_specials t2
                 else APP(IDENT s, remove_specials t2)
      | COMB (VAR s, f) => let
        in
          if s = fnapp_special then APP(remove_specials f, remove_specials t2)
          else if s = recsel_special then
            case t2 of
              VAR fldname => APP(IDENT (recsel_special ^ fldname),
                                 remove_specials f)
            | _ => raise ParseTermError
                "Record selection must have single id to right"
          else if s = reccons_special then
            remove_recupdate f t2 (IDENT "ARB")
          else if s = recwith_special then
            remove_recupdate' t2 (remove_specials f)
          else
            if s = recupd_special orelse s = recfupd_special then
              raise ParseTermError
                "May not use record update functions at top level"
            else
              APP(remove_specials t1, remove_specials t2)
        end
      | _ => APP(remove_specials t1, remove_specials t2)
    end
  | ABS(v, t2) => Absyn.LAM(to_vabsyn v, remove_specials t2)
  | TYPED(t, ty) => Absyn.TYPED(remove_specials t, ty)
  | VAR s => Absyn.IDENT s
  | QIDENT x => Absyn.QIDENT x
  | AQ x => Absyn.AQ x
and remove_recupdate upd1 updates bottom = let
  open Absyn
in
  case upd1 of
    COMB(COMB(VAR s, VAR fld), newvalue) => let
    in
      if s = recupd_special orelse s = recfupd_special then
        APP(APP(IDENT (s^fld), remove_specials newvalue),
             remove_recupdate' updates bottom)
      else raise ParseTermError recupd_errstring
    end
  | _ =>
    raise ParseTermError recupd_errstring
end
and remove_recupdate' updatelist bottom = let
  open Absyn
in
  case updatelist of
    VAR s => if s = recnil_special then bottom
             else raise ParseTermError recupd_errstring
  | COMB(COMB(VAR s, upd1), updates) => let
    in
      if s = reccons_special then remove_recupdate upd1 updates bottom
      else
        if s = recupd_special orelse s = recfupd_special then
          case upd1 of
            VAR fldname => APP(APP(IDENT (s^fldname),
                                     remove_specials updates),
                                bottom)
          | _ => raise ParseTermError
              "Must have field name as first argument to update operator"
        else
          raise ParseTermError recupd_errstring
    end
  | _ => raise ParseTermError recupd_errstring
end


fun top_nonterminal pstack =
  case pstack of
    PStack {stack = (NonTerminal pt, _)::_, ...} => remove_specials pt
  | _ => raise ParseTermError "No non-terminal on top of stack"

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
        pop >> push (NonTerminal(remove_specials t), Token (Ident "XXX"))
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
