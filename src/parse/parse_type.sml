structure parse_type :> parse_type =
struct

open type_tokens HOLgrammars monadic_parse optmonad

infix >- ++ >> >->

datatype grammar_rule =
  SUFFIX of string list
| INFIX of {opname : string, parse_string : string} list * associativity

val std_suffix_precedence = 100

type grammar = (int * grammar_rule) list
type 'a token = 'a type_token



fun parse_type tyfns allow_unknown_suffixes G = let
  val {vartype = pVartype, tyop = pType, antiq = pAQ, qtyop} = tyfns
  val lex = type_tokens.lex
  (* extra fails on next two definitions will effectively make the stream
     push back the unwanted token *)
  fun itemP P = (lex >- (fn t => if P t then return t else fail)) ++ fail

  (* can't use item for these, because this would require the token type
     to be an equality type, which is icky *)
  fun is_LParen t = case t of LParen => true | _ => false
  fun is_RParen t = case t of RParen => true | _ => false
  fun is_Comma t = case t of Comma => true | _ => false

  fun apply_tyop t args =
    case t of
      TypeIdent s => pType(s,args)
    | QTypeIdent(thy,ty) => qtyop{Thy=thy,Tyop=ty,Args=args}
    | _ => raise Fail "parse_type.apply_tyop: can't happen"

  fun n_appls (ops, t) =
    case ops of
      [] => t
    | oph::opt => n_appls (opt, apply_tyop oph [t])
  fun n_appls_l ([], t) = raise Fail "parse_type.n_appls_l: can't happen"
    | n_appls_l (op1::ops, xs) = n_appls (ops, apply_tyop op1 xs)
  fun parse_base_level f =
    lex >-
    (fn t =>
     case t of
       TypeIdent s => return (pType(s, []))
     | QTypeIdent(thy,ty) => return (qtyop{Thy = thy, Tyop = ty, Args = []})
     | TypeVar s => return (pVartype s)
     | AQ x => return (pAQ x)
     | LParen => (f >-> itemP is_RParen)
     | _ => fail)

  fun parse_op slist =
    lex >-
    (fn t =>
     case t of
       TypeIdent s =>
         if allow_unknown_suffixes orelse Lib.mem s slist then return t
         else fail
     | QTypeIdent _ => return t
     | _ => fail)
  fun parse_binop stlist = let
    fun doit t = let
      val result =
        List.find (fn r => (#parse_string r = token_string t)) stlist
    in
      case result of
        NONE => fail
      | SOME r => return (#opname r)
    end
  in
    (itemP is_ident ++ itemP is_typesymbol) >-  doit
  end


  fun parse_term current strm =
    (case current of
       [] => parse_base_level (parse_term G)
     | (x::xs) => parse_rule x xs) strm
  and parse_rule (r as (level, rule)) rs strm = let
    val next_level = parse_term rs
    val same_level = parse_rule r rs
    val tuple_arg =
      itemP is_LParen >>
      chainl1
      (parse_term G >- (fn t => return [t]))
      (itemP is_Comma >> return (fn tl1 => fn tl2 => tl1 @ tl2)) >-
      (fn args => itemP is_RParen >> return args)
  in
    (case rule of
       INFIX (stlist, NONASSOC) =>
         next_level >-                         (fn t1 =>
         (parse_binop stlist >-                (fn opname =>
          next_level >-                        (fn t2 =>
          return (pType(opname, [t1, t2]))))) ++
         (return t1))
     | INFIX (stlist, LEFT) =>
         chainl1 next_level
         (parse_binop stlist >-
          (fn opname => return (fn t1 => fn t2 => pType(opname, [t1, t2]))))
     | INFIX (stlist, RIGHT) =>
         chainr1 next_level
         (parse_binop stlist >-
          (fn opname => return (fn t1 => fn t2 => pType(opname, [t1, t2]))))
     | SUFFIX slist =>
         (next_level >-                             (fn t =>
          many (parse_op slist) >-                  (fn oplist =>
          return (n_appls (oplist, t))))) ++
         (tuple_arg >-                              (fn args =>
          many1 (parse_op slist) >-                 (fn oplist =>
          return (n_appls_l (oplist, args)))))) strm
  end
in
  parse_term G
end

fun merge r1 r2 =
  case (r1, r2) of
    (SUFFIX slist1, SUFFIX slist2) => SUFFIX(Lib.union slist1 slist2)
  | (INFIX(rlist1, a1), INFIX(rlist2, a2)) => let
    in
      if a1 = a2 then INFIX(Lib.union rlist1 rlist2, a1)
      else
        raise GrammarError
          "Attempt to merge two infix types with different associativities"
    end
  | _ => raise GrammarError "Attempt to merge suffix and infix type"

fun insert_sorted0 (k, v) [] = [(k, v)]
  | insert_sorted0 kv1 (wholething as (kv2::rest)) = let
      val (k1, v1) = kv1
      val (k2, v2) = kv2
    in
      if (k1 < k2) then kv1::wholething
      else
        if k1 = k2 then  (k1, merge v1 v2) :: rest
        else
          kv2 :: insert_sorted0 kv1 rest
    end

fun insert_sorted (k, v) G0 = let
  val G1 = insert_sorted0 (k,v) G0
  fun merge_adj_suffixes [] = []
    | merge_adj_suffixes [x] = [x]
    | merge_adj_suffixes (x1::x2::xs) = let
      in
        case (x1, x2) of
          ((p1, SUFFIX slist1), (p2, SUFFIX slist2)) =>
            merge_adj_suffixes ((p1, SUFFIX (Lib.union slist1 slist2))::xs)
        | _ => x1 :: merge_adj_suffixes (x2 :: xs)
      end
in
  merge_adj_suffixes G1
end



fun new_binary_tyop G {precedence, infix_form, opname, associativity} = let
  val rule1 =
    if isSome infix_form then
      (precedence, INFIX([{parse_string = valOf infix_form,
                           opname = opname}],
                         associativity))
    else (precedence, INFIX([{parse_string = opname, opname = opname}],
                            associativity))
  val rule2 = (std_suffix_precedence, SUFFIX[opname])
in
  insert_sorted rule1 (insert_sorted rule2 G)
end

fun new_tyop G name =
  insert_sorted (std_suffix_precedence, SUFFIX[name]) G

val empty_grammar = []

fun rules (G: grammar) = G

fun rev_append [] acc = acc
  | rev_append (x::xs) acc = rev_append xs (x::acc)

fun merge_grammars (G1:grammar, G2:grammar) = let
  (* both grammars are sorted, with no adjacent suffixes *)
  fun merge_acc acc (gs as (g1, g2)) =
    case gs of
      ([], _) => rev_append acc g2
    | (_, []) => rev_append acc g1
    | ((g1rule as (g1k, g1v))::g1rest, (g2rule as (g2k, g2v))::g2rest) => let
      in
        case Int.compare (g1k, g2k) of
          LESS => merge_acc (g1rule::acc) (g1rest, g2)
        | GREATER => merge_acc (g2rule::acc) (g1, g2rest)
        | EQUAL => merge_acc ((g1k, merge g1v g2v)::acc) (g1rest, g2rest)
      end
in
  merge_acc [] (G1, G2)
end

end;
